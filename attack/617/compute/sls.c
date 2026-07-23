/* sls.c — WalkSAT/tabu local search for Erdős #617, r=5, n=26.
 *
 * Goal: 5-coloring of E(K_26) such that every 6-subset induces all 5 colors,
 * i.e. alpha(G_c) <= 5 for every color class.
 *
 * Objective: sum over all C(26,6)=230230 6-sets S of (number of colors
 * missing among S's 15 edges).  Objective 0 <=> counterexample.
 * Equals core.violations() (sum over colors of independent 6-sets per class).
 *
 * Move: pick a random violated 6-set S and a missing color b; recoloring any
 * of S's 15 edges to b fixes (S,b).  With prob `noise` recolor a random edge
 * of S; otherwise the edge minimizing the objective delta (tabu on undoing
 * recent recolors, aspiration on new global best).  Always accept.
 * Reload global best after prolonged stagnation, with small perturbation.
 *
 * Usage: ./sls <seed_mode:0 rand|1 turan|2 ag25> <rng_seed> <noise>
 *              <out_prefix> [max_seconds]
 *        ./sls score <file-with-325-colors>
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#ifndef N
#define N 26
#endif
#define R 5
#define NE (N*(N-1)/2)
#if N == 26
#define NS 230230
#define SPE 10626 /* C(24,4): 6-sets containing a fixed edge */
#elif N == 25
#define NS 177100
#define SPE 8855  /* C(23,4) */
#else
#error "unsupported N"
#endif

static uint16_t set_edges[NS][15];
static int32_t (*edge_sets)[SPE];
static int edge_fill[NE];
static uint8_t cnt[NS][R];
static uint8_t missing[NS];
static uint8_t color[NE];
static uint8_t best_color[NE];
static int32_t viol_list[NS];
static int32_t viol_pos[NS];
static int nviol;
static long long objective, best_obj;
static long long tabu_until[NE][R];

static int eid[N][N];

static uint64_t rng_state;
static inline uint64_t rng_next(void) {
    uint64_t x = rng_state;
    x ^= x >> 12; x ^= x << 25; x ^= x >> 27;
    rng_state = x;
    return x * 0x2545F4914F6CDD1DULL;
}
static inline uint32_t rng_below(uint32_t n) { return (uint32_t)(rng_next() % n); }
static inline double rng_uniform(void) { return (rng_next() >> 11) * (1.0 / 9007199254740992.0); }

static double now_sec(void) {
    struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

static void build_tables(void) {
    int k = 0;
    for (int u = 0; u < N; u++)
        for (int v = u + 1; v < N; v++) { eid[u][v] = eid[v][u] = k++; }
    edge_sets = malloc(sizeof(int32_t) * NE * SPE);
    if (!edge_sets) { fprintf(stderr, "alloc fail\n"); exit(1); }
    memset(edge_fill, 0, sizeof edge_fill);
    int s = 0;
    int v[6];
    for (v[0] = 0; v[0] < N; v[0]++)
    for (v[1] = v[0]+1; v[1] < N; v[1]++)
    for (v[2] = v[1]+1; v[2] < N; v[2]++)
    for (v[3] = v[2]+1; v[3] < N; v[3]++)
    for (v[4] = v[3]+1; v[4] < N; v[4]++)
    for (v[5] = v[4]+1; v[5] < N; v[5]++) {
        int t = 0;
        for (int i = 0; i < 6; i++)
            for (int j = i+1; j < 6; j++) {
                int e = eid[v[i]][v[j]];
                set_edges[s][t++] = (uint16_t)e;
                edge_sets[e][edge_fill[e]++] = s;
            }
        s++;
    }
    if (s != NS) { fprintf(stderr, "NS mismatch %d\n", s); exit(1); }
    for (int e = 0; e < NE; e++)
        if (edge_fill[e] != SPE) { fprintf(stderr, "SPE mismatch\n"); exit(1); }
}

static void recompute_all(void) {
    memset(cnt, 0, sizeof cnt);
    objective = 0; nviol = 0;
    for (int s = 0; s < NS; s++)
        for (int t = 0; t < 15; t++)
            cnt[s][color[set_edges[s][t]]]++;
    for (int s = 0; s < NS; s++) {
        int m = 0;
        for (int c = 0; c < R; c++) if (cnt[s][c] == 0) m++;
        missing[s] = (uint8_t)m;
        objective += m;
        if (m > 0) { viol_pos[s] = nviol; viol_list[nviol++] = s; }
        else viol_pos[s] = -1;
    }
}

static inline void viol_add(int s) { viol_pos[s] = nviol; viol_list[nviol++] = s; }
static inline void viol_remove(int s) {
    int p = viol_pos[s];
    int last = viol_list[--nviol];
    viol_list[p] = last; viol_pos[last] = p;
    viol_pos[s] = -1;
}

static long long move_delta(int e, int a, int b) {
    long long d = 0;
    const int32_t *lst = edge_sets[e];
    for (int i = 0; i < SPE; i++) {
        int s = lst[i];
        d += (cnt[s][a] == 1);
        d -= (cnt[s][b] == 0);
    }
    return d;
}

static void move_commit(int e, int a, int b) {
    const int32_t *lst = edge_sets[e];
    for (int i = 0; i < SPE; i++) {
        int s = lst[i];
        if (--cnt[s][a] == 0) {
            if (missing[s] == 0) viol_add(s);
            missing[s]++; objective++;
        }
        if (cnt[s][b]++ == 0) {
            missing[s]--; objective--;
            if (missing[s] == 0) viol_remove(s);
        }
    }
    color[e] = (uint8_t)b;
}

/* ---------- seeds ---------- */
static void shuffle(int *a, int n) {
    for (int i = n - 1; i > 0; i--) { int j = rng_below(i + 1); int t = a[i]; a[i] = a[j]; a[j] = t; }
}

static void seed_random(void) { for (int e = 0; e < NE; e++) color[e] = rng_below(R); }

static void seed_turan(void) {
    int part[R][N];
    for (int c = 0; c < R; c++) {
        int perm[N]; for (int i = 0; i < N; i++) perm[i] = i;
        shuffle(perm, N);
        int idx = 0;
        for (int p = 0; p < 5; p++) {
            int sz = (p == 0) ? 6 : 5;
            for (int i = 0; i < sz; i++) part[c][perm[idx++]] = p;
        }
    }
    for (int u = 0; u < N; u++)
        for (int v = u + 1; v < N; v++) {
            int cand[R], nc = 0;
            for (int c = 0; c < R; c++) if (part[c][u] == part[c][v]) cand[nc++] = c;
            color[eid[u][v]] = nc ? cand[rng_below(nc)] : rng_below(R);
        }
}

static void seed_ag25(void) {
    /* AG(2,5) on vertices 0..24 = (x,y) -> 5x+y.
       color 0 = rows+columns (rook graph, alpha=5);
       colors m=1..4 = parallel class of slope m (5 disjoint K5, alpha=5);
       vertex 25's edges random. */
    static const int inv[5] = {0, 1, 3, 2, 4};
    for (int u = 0; u < 25; u++)
        for (int v = u + 1; v < 25; v++) {
            int x1 = u / 5, y1 = u % 5, x2 = v / 5, y2 = v % 5;
            int c;
            if (x1 == x2 || y1 == y2) c = 0;
            else c = (((y2 - y1 + 5) % 5) * inv[(x2 - x1 + 5) % 5]) % 5;
            color[eid[u][v]] = (uint8_t)c;
        }
    for (int u = 0; u < 25; u++) color[eid[u][25]] = rng_below(R);
}

static void seed_circulant(void) {
    /* color by difference class (v-u) mod 26; 13 difference classes
       {±1..±12, 13} assigned near-evenly at random to 5 colors.
       Each class is a circulant graph (Paley-like candidate structure). */
    int nd = N / 2; /* number of difference classes */
    int dc[N/2 + 1];
    int order[N/2]; for (int i = 0; i < nd; i++) order[i] = i + 1;
    shuffle(order, nd);
    for (int i = 0; i < nd; i++) dc[order[i]] = i % R;
    for (int u = 0; u < N; u++)
        for (int v = u + 1; v < N; v++) {
            int d = v - u; if (d > nd) d = N - d;
            color[eid[u][v]] = (uint8_t)dc[d];
        }
}

static void save_best(const char *prefix) {
    char path[512]; snprintf(path, sizeof path, "%s.best.txt", prefix);
    FILE *f = fopen(path, "w");
    if (!f) return;
    fprintf(f, "%lld\n", best_obj);
    for (int e = 0; e < NE; e++) fprintf(f, "%d%c", best_color[e], e == NE-1 ? '\n' : ' ');
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc == 3 && strcmp(argv[1], "score") == 0) {
        FILE *f = fopen(argv[2], "r");
        if (!f) { perror("open"); return 2; }
        for (int e = 0; e < NE; e++) { int c; if (fscanf(f, "%d", &c) != 1) return 2; color[e] = (uint8_t)c; }
        fclose(f);
        build_tables();
        recompute_all();
        printf("%lld\n", objective);
        return 0;
    }
    if (argc < 5) {
        fprintf(stderr, "usage: %s seed_mode rng_seed noise out_prefix "
                        "[max_seconds] [sample_k] [reload_after] [drift]\n", argv[0]);
        return 2;
    }
    int seed_mode = atoi(argv[1]);
    rng_state = strtoull(argv[2], NULL, 10) * 2654435761ULL + 88172645463325252ULL;
    double noise = atof(argv[3]);
    const char *prefix = argv[4];
    double max_sec = argc > 5 ? atof(argv[5]) : 1e18;
    int sample_k = argc > 6 ? atoi(argv[6]) : 4;
    long long reload_after = argc > 7 ? atoll(argv[7]) : 40000;
    long long drift = argc > 8 ? atoll(argv[8]) : 600;

    build_tables();
    if (seed_mode == 1) seed_turan();
    else if (seed_mode == 2) seed_ag25();
    else if (seed_mode == 3) seed_circulant();
    else seed_random();
    recompute_all();
    memset(tabu_until, 0, sizeof tabu_until);

    memcpy(best_color, color, NE);
    best_obj = objective;
    save_best(prefix);
    printf("init: seed_mode=%d obj=%lld nviol=%d noise=%.2f\n",
           seed_mode, objective, nviol, noise);
    fflush(stdout);

    const long long CHECK_EVERY = 20000000;

    double t_start = now_sec(), t_last = t_start;
    long long moves = 0, last_improve = 0, reloads = 0;

    while (nviol > 0) {
        moves++;
        int e, a, b;
        if (rng_uniform() < noise) {
            int s = viol_list[rng_below(nviol)];
            int miss[R], nm = 0;
            for (int c = 0; c < R; c++) if (cnt[s][c] == 0) miss[nm++] = c;
            b = miss[rng_below(nm)];
            e = set_edges[s][rng_below(15)];
            a = color[e];
        } else {
            long long bd = 0; int be = -1, bb = -1, nties = 0;
            int ks = sample_k < nviol ? sample_k : nviol;
            for (int q = 0; q < ks; q++) {
                int s = viol_list[rng_below(nviol)];
                int miss[R], nm = 0;
                for (int c = 0; c < R; c++) if (cnt[s][c] == 0) miss[nm++] = c;
                int cb = miss[rng_below(nm)];
                for (int t = 0; t < 15; t++) {
                    int ce = set_edges[s][t];
                    int ca = color[ce];
                    long long d = move_delta(ce, ca, cb);
                    int is_tabu = tabu_until[ce][cb] > moves &&
                                  objective + d >= best_obj;
                    if (is_tabu) continue;
                    if (be < 0 || d < bd) { bd = d; be = ce; bb = cb; nties = 1; }
                    else if (d == bd) { nties++; if (rng_below(nties) == 0) { be = ce; bb = cb; } }
                }
            }
            if (be < 0) { /* all tabu: random repair */
                int s = viol_list[rng_below(nviol)];
                int miss[R], nm = 0;
                for (int c = 0; c < R; c++) if (cnt[s][c] == 0) miss[nm++] = c;
                bb = miss[rng_below(nm)];
                be = set_edges[s][rng_below(15)];
            }
            e = be; b = bb;
            a = color[e];
        }
        move_commit(e, a, b);
        tabu_until[e][a] = moves + 10 + nviol / 64 + rng_below(10);

        if (objective < best_obj) {
            best_obj = objective;
            memcpy(best_color, color, NE);
            save_best(prefix);
            last_improve = moves;
            if (best_obj == 0) {
                printf("!!!! WITNESS FOUND obj=0 moves=%lld t=%.1fs !!!!\n",
                       moves, now_sec() - t_start);
                fflush(stdout);
                return 0;
            }
        }
        if (moves - last_improve > reload_after ||
            (moves - last_improve > 5000 && objective > best_obj + drift)) {
            /* reload best + perturb a few random edges (commit-based) */
            memcpy(color, best_color, NE);
            recompute_all();
            int np = 2 + rng_below(4);
            for (int i = 0; i < np; i++) {
                int pe = rng_below(NE), pa = color[pe];
                int pb = rng_below(R - 1); if (pb >= pa) pb++;
                move_commit(pe, pa, pb);
            }
            memset(tabu_until, 0, sizeof tabu_until);
            last_improve = moves;
            reloads++;
            if ((reloads & 0x3F) == 1) {
                printf("reload#%lld: best=%lld obj=%lld moves=%lld\n",
                       reloads, best_obj, objective, moves);
                fflush(stdout);
            }
        }
        if ((moves & 0x3FF) == 0) {
            double t = now_sec();
            if (t - t_last > 30.0) {
                printf("stat: t=%.0fs moves=%lld obj=%lld best=%lld nviol=%d\n",
                       t - t_start, moves, objective, best_obj, nviol);
                fflush(stdout);
                t_last = t;
            }
            if (t - t_start > max_sec) {
                printf("timeout: best=%lld moves=%lld\n", best_obj, moves);
                return 0;
            }
        }
        if (moves % CHECK_EVERY == 0) {
            long long saved = objective;
            recompute_all();
            if (objective != saved) {
                printf("CONSISTENCY FAILURE %lld vs %lld\n", saved, objective);
                return 1;
            }
        }
    }
    printf("!!!! WITNESS FOUND (loop exit) obj=%lld !!!!\n", objective);
    return 0;
}
