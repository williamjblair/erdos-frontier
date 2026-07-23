/* Focused annealer for Erdos #617 r=5 n=26 (variant b).
 * Objective: total independent 6-sets across the 5 classes (0 = win).
 * Moves: with prob 60% focused (find an independent 6-set in a random class c,
 * recolor a random internal pair to c), else random single-edge recolor.
 * Metropolis acceptance on exact incremental delta.
 * Usage: ./anneal617b <seed> <iters> [start.txt]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>

#define N 26
#define R 5
#define E 325
static int EU[E], EV[E], EID[N][N];
static uint32_t adj[R][N];
static int color[E];
static const uint32_t FULL = (1u << N) - 1;

static int popcount(uint32_t x) { return __builtin_popcount(x); }

static long count_ind(int c, uint32_t cand, int k) {
    if (k == 0) return 1;
    if (k == 1) return popcount(cand);
    long total = 0;
    while (cand) {
        int v = __builtin_ctz(cand);
        cand &= cand - 1;
        if (popcount(cand) < k - 1) break;
        uint32_t nc = cand & ~adj[c][v];
        if (popcount(nc) >= k - 1) total += count_ind(c, nc, k - 1);
    }
    return total;
}

static long class_count6(int c) { return count_ind(c, FULL, 6); }

/* find one independent 6-set in class c starting DFS at a random vertex
 * permutation offset; fills found_set, returns 1 if found */
static int found_set[6];
static int perm_order[N];
static int dfs_find(int c, uint32_t cand, int k) {
    if (k == 0) return 1;
    for (int i = 0; i < N; i++) {
        int v = perm_order[i];
        if (!((cand >> v) & 1)) continue;
        cand &= ~(1u << v); /* v now processed: sets w/o v use remaining */
        if (popcount(cand) + 1 < k) return 0;
        uint32_t nc = cand & ~adj[c][v];
        if (popcount(nc) >= k - 1) {
            found_set[6 - k] = v;
            if (dfs_find(c, nc, k - 1)) return 1;
        }
    }
    return 0;
}

static long pair_count(int c, int u, int v) {
    if ((adj[c][u] >> v) & 1) return 0;
    uint32_t cand = FULL & ~adj[c][u] & ~adj[c][v] & ~(1u << u) & ~(1u << v);
    return count_ind(c, cand, 4);
}

int main(int argc, char **argv) {
    unsigned seed = argc > 1 ? (unsigned)atoi(argv[1]) : 1;
    long iters = argc > 2 ? atol(argv[2]) : 2000000000L;
    srandom(seed);
    int k = 0;
    for (int u = 0; u < N; u++)
        for (int v = u + 1; v < N; v++) { EU[k] = u; EV[k] = v; EID[u][v] = EID[v][u] = k; k++; }

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
    long cnt[R], obj = 0;
    for (int c = 0; c < R; c++) { cnt[c] = class_count6(c); obj += cnt[c]; }
    fprintf(stderr, "seed %u initial obj %ld\n", seed, obj);
    long best = obj;
    int bestcol[E];
    memcpy(bestcol, color, sizeof bestcol);
    double T = 3.0;
    long since = 0;
    for (long it = 0; it < iters && best > 0; it++) {
        int e = -1, c2 = -1;
        if (random() % 100 < 60) {
            /* pick a violated class weighted by count */
            int c = -1;
            long tot = obj > 0 ? obj : 1;
            long r = random() % tot, acc = 0;
            for (int cc = 0; cc < R; cc++) { acc += cnt[cc]; if (r < acc) { c = cc; break; } }
            if (c >= 0 && cnt[c] > 0) {
                int off = random() % N;
                for (int i = 0; i < N; i++) perm_order[i] = (i + off) % N;
                if (dfs_find(c, FULL, 6)) {
                    int a = random() % 6, b = random() % 6;
                    while (b == a) b = random() % 6;
                    e = EID[found_set[a]][found_set[b]];
                    c2 = c;
                }
            }
        }
        if (e < 0) { e = random() % E; c2 = random() % R; }
        int c = color[e];
        if (c2 == c) continue;
        int u = EU[e], v = EV[e];
        adj[c][u] &= ~(1u << v); adj[c][v] &= ~(1u << u);
        long gain = pair_count(c, u, v);
        long kill = pair_count(c2, u, v);
        long delta = gain - kill;
        if (delta <= 0 || (double)random() / RAND_MAX < exp(-delta / T)) {
            color[e] = c2;
            adj[c2][u] |= 1u << v; adj[c2][v] |= 1u << u;
            obj += delta;
            cnt[c] += gain; cnt[c2] -= kill;
            if (obj < best) {
                best = obj; memcpy(bestcol, color, sizeof bestcol); since = 0;
                if (best == 0) break;
            }
        } else {
            adj[c][u] |= 1u << v; adj[c][v] |= 1u << u;
        }
        since++;
        if ((it & 0xFFFF) == 0) { T *= 0.9995; if (T < 0.15) T = 0.15; }
        if (since > 20000000L) { T = 2.5; since = 0; }
        if ((it & 0xFFFFFF) == 0) {
            long chk = 0;
            for (int cc = 0; cc < R; cc++) { cnt[cc] = class_count6(cc); chk += cnt[cc]; }
            if (chk != obj) fprintf(stderr, "DRIFT %ld vs %ld\n", chk, obj);
            obj = chk;
            fprintf(stderr, "seed %u it %ld obj %ld best %ld T %.3f\n",
                    seed, it, obj, best, T);
        }
    }
    printf("seed %u best %ld\n", seed, best);
    char fn[64];
    snprintf(fn, sizeof fn, "bestb_%u.txt", seed);
    FILE *f = fopen(fn, "w");
    for (int i = 0; i < E; i++) fputc('0' + bestcol[i], f);
    fclose(f);
    return best == 0 ? 0 : 1;
}
