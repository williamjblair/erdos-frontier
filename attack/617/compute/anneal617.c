/* General annealer for Erdos #617 r=5 n=26: minimize total number of
 * independent 6-sets across the 5 color classes (0 == counterexample).
 * Incremental delta: flipping edge (u,v) c->c' changes counts only via
 * 6-sets containing both u and v in classes c (gained) and c' (killed):
 * each delta = #independent-4-sets among common non-neighbors (bitmask DFS).
 * Usage: ./anneal617 <seed> <iters> [start.txt]   (start: 325 digits 0-4)
 * Prints best objective found; writes best coloring to best_<seed>.txt.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>

#define N 26
#define R 5
#define E 325
static int EU[E], EV[E];
static uint32_t adj[R][N]; /* neighbours within color class */
static int color[E];
static const uint32_t FULL = (1u << N) - 1;

static int popcount(uint32_t x) { return __builtin_popcount(x); }

/* count independent k-sets of class c inside candidate mask */
static long count_ind(int c, uint32_t cand, int k) {
    if (k == 0) return 1;
    if (k == 1) return popcount(cand);
    long total = 0;
    while (cand) {
        int v = __builtin_ctz(cand);
        cand &= cand - 1;
        if (popcount(cand) < k - 1) break; /* not enough left for any later v */
        uint32_t nc = cand & ~adj[c][v];
        if (popcount(nc) >= k - 1) total += count_ind(c, nc, k - 1);
    }
    return total;
}

static long class_count6(int c) { return count_ind(c, FULL, 6); }

/* # independent 6-sets of class c containing both u,v assuming uv NOT an edge */
static long pair_count(int c, int u, int v) {
    uint32_t cand = FULL & ~adj[c][u] & ~adj[c][v] & ~(1u << u) & ~(1u << v);
    if ((adj[c][u] >> v) & 1) return 0; /* uv is an edge: none */
    return count_ind(c, cand, 4);
}

int main(int argc, char **argv) {
    unsigned seed = argc > 1 ? (unsigned)atoi(argv[1]) : 1;
    long iters = argc > 2 ? atol(argv[2]) : 200000000L;
    srandom(seed);
    int k = 0;
    for (int u = 0; u < N; u++)
        for (int v = u + 1; v < N; v++) { EU[k] = u; EV[k] = v; k++; }

    if (argc > 3) {
        FILE *f = fopen(argv[3], "r");
        for (int i = 0; i < E; i++) { int ch = fgetc(f); color[i] = ch - '0'; }
        fclose(f);
    } else {
        for (int i = 0; i < E; i++) color[i] = random() % R;
    }
    memset(adj, 0, sizeof adj);
    for (int i = 0; i < E; i++) {
        adj[color[i]][EU[i]] |= 1u << EV[i];
        adj[color[i]][EV[i]] |= 1u << EU[i];
    }
    long obj = 0;
    for (int c = 0; c < R; c++) obj += class_count6(c);
    fprintf(stderr, "seed %u initial obj %ld\n", seed, obj);
    long best = obj;
    int bestcol[E];
    memcpy(bestcol, color, sizeof bestcol);
    double T = 8.0;
    long since = 0;
    for (long it = 0; it < iters && best > 0; it++) {
        int e = random() % E;
        int c = color[e], c2 = random() % R;
        if (c2 == c) continue;
        int u = EU[e], v = EV[e];
        /* remove from c: gain = pair_count after removal */
        adj[c][u] &= ~(1u << v); adj[c][v] &= ~(1u << u);
        long gain = pair_count(c, u, v);
        long kill = pair_count(c2, u, v);
        long delta = gain - kill;
        if (delta <= 0 || (double)random() / RAND_MAX < exp(-delta / T)) {
            color[e] = c2;
            adj[c2][u] |= 1u << v; adj[c2][v] |= 1u << u;
            obj += delta;
            if (obj < best) {
                best = obj; memcpy(bestcol, color, sizeof bestcol); since = 0;
                if (best == 0) break;
            }
        } else { /* revert */
            adj[c][u] |= 1u << v; adj[c][v] |= 1u << u;
        }
        since++;
        if ((it & 0xFFFF) == 0) {
            T *= 0.999;
            if (T < 0.05) T = 0.05;
        }
        if (since > 30000000L) { /* reheat / partial restart */
            T = 6.0; since = 0;
        }
        if ((it & 0xFFFFFF) == 0) {
            long chk = 0;
            for (int cc = 0; cc < R; cc++) chk += class_count6(cc);
            obj = chk;
            fprintf(stderr, "seed %u it %ld obj %ld best %ld T %.3f\n",
                    seed, it, obj, best, T);
        }
    }
    printf("seed %u best %ld\n", seed, best);
    char fn[64];
    snprintf(fn, sizeof fn, "best_%u.txt", seed);
    FILE *f = fopen(fn, "w");
    for (int i = 0; i < E; i++) fputc('0' + bestcol[i], f);
    fclose(f);
    return best == 0 ? 0 : 1;
}
