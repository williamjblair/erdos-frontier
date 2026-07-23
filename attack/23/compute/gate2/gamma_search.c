/* gamma_search.c — exhaustive Gamma-invariant scan (Erdős #23 gate 2).
 *
 * stdin:  graph6 lines from `geng -q -c -t n` (connected triangle-free).
 * argv:   n  [dumpfile]  [dump_thresh_numer]  — dump instances "g6 S" when
 *         |M|>=1 and (n <= 10 or Gamma >= (n-1)^2).
 *
 * For each graph: exact max cut over all 2^(n-1) colourings (Gray code),
 * then every colouring attaining mc is processed as an instance (G,S):
 *   - ASSERT B connected + spanning         (theorem S7': G connected => B connected)
 *   - ASSERT every M-edge has d_B even, >= 4 (theorems S4/S5)
 *   - ASSERT d_M(v) <= d_B(v) for all v      (theorem S3)
 *   - Gamma = sum (d_B(u,v)+1)^2 over M;  check Gamma <= n^2.
 * Reports: counterexamples (CEX), equality cases (EQ), per-n stats,
 * and the largest non-equal Gamma with witness.
 * All arithmetic integer-exact. Single-threaded.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int n, nedges;
static unsigned adj[16];
static int eu[80], ev[80];
static char g6[64];

static long long ninst = 0, ninstM = 0, neq = 0, ncex = 0, ngraphs = 0;
static long long maxgap_gamma = -1, nl1 = 0, nc9 = 0; /* largest Gamma among non-equal instances */
static char maxgap_g6[64]; static unsigned maxgap_S; static int maxgap_n2;
static FILE *dumpf = NULL;
static int dump_all_upto;   /* dump all M!=0 instances if n <= this */
static long long ndump = 0;

static int decode_g6(const char *line) {
    int c = line[0] - 63;
    if (c < 1 || c > 15) return -1;
    n = c;
    memset(adj, 0, sizeof adj);
    nedges = 0;
    int p = 0, i = 0, j = 1, len = strlen(line);
    for (int b = 1; b < len; b++) {
        int x = line[b] - 63;
        for (int k = 5; k >= 0; k--) {
            if (j >= n) break;
            if ((x >> k) & 1) {
                adj[i] |= 1u << j; adj[j] |= 1u << i;
                eu[nedges] = i; ev[nedges] = j; nedges++;
            }
            if (++i == j) { i = 0; j++; }
            p++;
        }
    }
    return 0;
}

static int bfs_dist(unsigned *badj, int src, int dst) {
    int dist[16], q[16], qh = 0, qt = 0;
    for (int v = 0; v < n; v++) dist[v] = -1;
    dist[src] = 0; q[qt++] = src;
    while (qh < qt) {
        int x = q[qh++];
        unsigned m = badj[x];
        while (m) {
            int y = __builtin_ctz(m); m &= m - 1;
            if (dist[y] < 0) { dist[y] = dist[x] + 1; if (y == dst) return dist[y]; q[qt++] = y; }
        }
    }
    return dist[dst];
}

static void process(unsigned S, int mc) {
    unsigned full = (1u << n) - 1, comp = full & ~S;
    unsigned badj[16];
    int nm = 0, mu[80], mv[80];
    ninst++;
    for (int v = 0; v < n; v++)
        badj[v] = adj[v] & (((S >> v) & 1) ? comp : S);
    /* S3: d_M(v) <= d_B(v) */
    for (int v = 0; v < n; v++) {
        int dB = __builtin_popcount(badj[v]);
        int dM = __builtin_popcount(adj[v]) - dB;
        if (dM > dB) { printf("VIOLATION-S3 %s S=%u v=%d\n", g6, S, v); exit(2); }
    }
    for (int e = 0; e < nedges; e++)
        if (((S >> eu[e]) & 1) == ((S >> ev[e]) & 1)) { mu[nm] = eu[e]; mv[nm] = ev[e]; nm++; }
    /* S7': B connected + spanning (G is connected by geng -c) */
    unsigned reach = 1;
    for (;;) {
        unsigned nw = reach, m = reach;
        while (m) { int v = __builtin_ctz(m); m &= m - 1; nw |= badj[v]; }
        if (nw == reach) break;
        reach = nw;
    }
    if (reach != full) { printf("VIOLATION-S7 %s S=%u\n", g6, S); exit(2); }
    if (nm == 0) return;  /* Gamma = 0, trivial */
    ninstM++;
    long long gamma = 0, sum_d1 = 0; int dmax = 0;
    for (int e = 0; e < nm; e++) {
        int d = bfs_dist(badj, mu[e], mv[e]);
        if (d < 0)      { printf("VIOLATION-S7b %s S=%u\n", g6, S); exit(2); }
        if (d & 1)      { printf("VIOLATION-S4 %s S=%u\n", g6, S); exit(2); }
        if (d < 4)      { printf("VIOLATION-S5 %s S=%u\n", g6, S); exit(2); }
        gamma += (long long)(d + 1) * (d + 1);
        sum_d1 += d + 1;
        if (d > dmax) dmax = d;
    }
    int n2 = n * n;
    /* C2 L1 consequence:  sum (d+1) <= e(G) ;  violation kills C2 exactly */
    if (sum_d1 > nedges) { printf("L1VIOL %d %s %u sum=%lld e=%d\n", n, g6, S, sum_d1, nedges); nl1++; }
    /* C9 (Hoelder form):  (dmax+1) * sum (d+1) <= n^2 */
    if ((long long)(dmax + 1) * sum_d1 > n2) { printf("C9VIOL %d %s %u lhs=%lld n2=%d\n", n, g6, S, (long long)(dmax+1)*sum_d1, n2); nc9++; }
    if (gamma > n2) { printf("CEX %d %s %u mc=%d Gamma=%lld N2=%d\n", n, g6, S, mc, gamma, n2); ncex++; }
    else if (gamma == n2) { printf("EQ %d %s %u mc=%d |M|=%d Gamma=%lld\n", n, g6, S, mc, nm, gamma); neq++; }
    else if (gamma > maxgap_gamma) {
        maxgap_gamma = gamma; strcpy(maxgap_g6, g6); maxgap_S = S; maxgap_n2 = n2;
    }
    if (dumpf && (n <= dump_all_upto || gamma >= (long long)(n-1)*(n-1))) {
        fprintf(dumpf, "%s %u\n", g6, S);
        ndump++;
    }
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: gamma_search n [dumpfile] [dump_all_upto]\n"); return 1; }
    int expect_n = atoi(argv[1]);
    dump_all_upto = 10;
    if (argc >= 3) dumpf = fopen(argv[2], "w");
    if (argc >= 4) dump_all_upto = atoi(argv[3]);
    char line[128];
    while (fgets(line, sizeof line, stdin)) {
        int L = strlen(line);
        while (L && (line[L-1] == '\n' || line[L-1] == '\r')) line[--L] = 0;
        if (!L) continue;
        if (decode_g6(line)) { fprintf(stderr, "bad g6: %s\n", line); return 1; }
        if (n != expect_n) { fprintf(stderr, "n mismatch: %d vs %d\n", n, expect_n); return 1; }
        strcpy(g6, line);
        ngraphs++;
        unsigned half = 1u << (n - 1), full = (1u << n) - 1;
        /* pass 1: mc via Gray code */
        int mc = 0, cut = 0;   /* S = 0 -> cut 0 */
        unsigned S = 0;
        for (unsigned i = 1; i < half; i++) {
            int v = __builtin_ctz(i);
            unsigned same, opp;
            if ((S >> v) & 1) { same = S & ~(1u << v); opp = full & ~S; }
            else              { same = (full & ~S) & ~(1u << v); opp = S; }
            cut += __builtin_popcount(adj[v] & same) - __builtin_popcount(adj[v] & opp);
            S ^= 1u << v;
            if (cut > mc) mc = cut;
        }
        /* pass 2: process all argmax colourings */
        S = 0; cut = 0;
        if (cut == mc) process(S, mc);
        for (unsigned i = 1; i < half; i++) {
            int v = __builtin_ctz(i);
            unsigned same, opp;
            if ((S >> v) & 1) { same = S & ~(1u << v); opp = full & ~S; }
            else              { same = (full & ~S) & ~(1u << v); opp = S; }
            cut += __builtin_popcount(adj[v] & same) - __builtin_popcount(adj[v] & opp);
            S ^= 1u << v;
            if (cut == mc) process(S, mc);
        }
    }
    printf("SUMMARY n=%d graphs=%lld maxcut_instances=%lld withM=%lld EQ=%lld CEX=%lld L1VIOL=%lld C9VIOL=%lld dumped=%lld\n",
           expect_n, ngraphs, ninst, ninstM, neq, ncex, nl1, nc9, ndump);
    if (maxgap_gamma >= 0)
        printf("MAXNONEQ n=%d Gamma=%lld N2=%d g6=%s S=%u\n",
               expect_n, maxgap_gamma, maxgap_n2, maxgap_g6, maxgap_S);
    if (dumpf) fclose(dumpf);
    return ncex ? 3 : 0;
}
