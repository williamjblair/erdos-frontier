/* Gate-1 independent brute-force ground truth for arXiv:2606.28041 (Erdos #23).
 * Reads graph6 lines from stdin (use: geng -t <n> | ./brute_check <n>).
 * For every graph: exact max cut by Gray-code enumeration (vertex 0 fixed).
 * Reports: count; max beta = e - mc (a) over all graphs, (b) over the BCL band
 * 0.2486 <= e/C(n,2) <= 0.3197 (exact integer comparison); d_mono = 2 beta / n^2.
 * Independent of the author's Python (own decoder, own max-cut). Single-threaded.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: %s n\n", argv[0]); return 2; }
    int n = atoi(argv[1]);
    if (n < 2 || n > 20) { fprintf(stderr, "n out of range\n"); return 2; }
    long C2 = (long)n * (n - 1) / 2;
    long long count = 0;
    int best_all = -1, best_all_e = 0, best_all_mc = 0;
    int best_band = -1, best_band_e = 0, best_band_mc = 0;
    char line[256];
    unsigned adj[20];
    while (fgets(line, sizeof line, stdin)) {
        int len = (int)strlen(line);
        while (len && (line[len-1] == '\n' || line[len-1] == '\r')) line[--len] = 0;
        if (!len) continue;
        if (line[0] - 63 != n) { fprintf(stderr, "bad g6 header: %s\n", line); return 1; }
        memset(adj, 0, sizeof adj);
        int e = 0, bitpos = 0;
        /* graph6 upper triangle, column-major: (i,j) for j=1..n-1, i=0..j-1 */
        for (int j = 1; j < n; j++) {
            for (int i = 0; i < j; i++) {
                int byte = 1 + bitpos / 6, shift = 5 - bitpos % 6;
                if (byte >= len) { fprintf(stderr, "short g6 line\n"); return 1; }
                if (((line[byte] - 63) >> shift) & 1) {
                    adj[i] |= 1u << j; adj[j] |= 1u << i; e++;
                }
                bitpos++;
            }
        }
        /* Gray-code max cut: side set S over vertices 1..n-1 (vertex 0 in side 0) */
        unsigned S = 0;
        int cut = 0, best = 0;
        unsigned long long total = 1ULL << (n - 1);
        for (unsigned long long g = 1; g < total; g++) {
            int v = __builtin_ctzll(g) + 1;       /* vertex to flip (1-based) */
            unsigned full = (1u << n) - 1;
            if (S & (1u << v)) {                   /* v leaves S */
                S ^= 1u << v;
                cut += __builtin_popcount(adj[v] & S)
                     - __builtin_popcount(adj[v] & (~S & full & ~(1u << v)));
            } else {                               /* v joins S */
                cut += __builtin_popcount(adj[v] & (~S & full & ~(1u << v)))
                     - __builtin_popcount(adj[v] & S);
                S ^= 1u << v;
            }
            if (cut > best) best = cut;
        }
        int beta = e - best;
        if (beta > best_all) { best_all = beta; best_all_e = e; best_all_mc = best; }
        /* band test: 2486*C2 <= 10000*e <= 3197*C2, exact integers */
        if (10000L * e >= 2486L * C2 && 10000L * e <= 3197L * C2) {
            if (beta > best_band) { best_band = beta; best_band_e = e; best_band_mc = best; }
        }
        count++;
    }
    printf("n=%d graphs=%lld\n", n, count);
    printf("  ALL : max beta=%d (e=%d mc=%d)  d_mono=%.6f  => a(%d)=%d\n",
           best_all, best_all_e, best_all_mc, 2.0 * best_all / (n * n), n, best_all);
    if (best_band >= 0)
        printf("  BAND: max beta=%d (e=%d mc=%d d_edge=%.4f)  d_mono=%.6f  [target 0.08]\n",
               best_band, best_band_e, best_band_mc, (double)best_band_e / C2,
               2.0 * best_band / (n * n));
    else
        printf("  BAND: empty\n");
    return 0;
}
