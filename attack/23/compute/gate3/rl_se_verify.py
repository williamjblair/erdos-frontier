"""rl_se_verify.py — machine verification of the single-edge structural laws
that drive the |M| = 1 proof of Lemma RL, on exhaustive small instances.

For EVERY valid one-stub rooted instance (any |M| up to MMAX) and EVERY
M-edge {y,z} in it, and every choice of w–x0 geodesic P where relevant:

  SE1 : d_B(y,z) <= 2 s                        (s = n - 1 - d)
  SE2 : 2 d_B(y,z) <= 2 s + d
  G1  : the w-level window of {y,z} clipped to [1,d] satisfies
        |W| <= 2 * #{f in V \\ P : a(f) in [min(W)-1, max(W)]}   (per P)
  MSL : for every corridor edge e_k of P (k = 1..d), y and z lie in the
        same component of B - e_k                                 (per P)

Usage: python3 rl_se_verify.py NMAX MMAX
"""
import sys, time
from itertools import combinations
import numpy as np
from rl_lib import (parse_graph6, adj_masks, bfs_dist, all_dists,
                    m_candidates, union_triangle_free, xor_bits,
                    valid_stub_pairs, gen_bipartite, geodesics_between)

FAIL = 0


def fail(msg):
    global FAIL
    FAIL += 1
    print(f"*** SE FAILURE *** {msg}")


def same_comp_minus_edge(n, edges, e, y, z):
    e2 = [x for x in edges if x != e]
    adj = adj_masks(n, e2)
    return bfs_dist(n, adj, y)[z] >= 0


def main():
    nmax = int(sys.argv[1])
    mmax = int(sys.argv[2])
    t0 = time.time()
    checked = dict(se1=0, se2=0, g1=0, msl=0)
    for n in range(2, nmax + 1):
        bit = xor_bits(n)
        for line in gen_bipartite(n):
            nn, edges = parse_graph6(line)
            adj = adj_masks(n, edges)
            dist = all_dists(n, edges)
            mcand = m_candidates(n, dist)
            if not mcand:
                continue
            ebase = np.zeros(1 << n, dtype=np.int32)
            for a, b in edges:
                ebase += bit[a] ^ bit[b]
            xr = {e: bit[e[0]] ^ bit[e[1]] for e in mcand}
            kmax = len(mcand) if mmax == 0 else mmax
            msets = []
            for k in range(1, kmax + 1):
                msets.extend(combinations(mcand, k))
            for M in msets:
                if len(M) > 1 and not union_triangle_free(n, edges, M):
                    continue
                sl = ebase.copy()
                for e in M:
                    sl -= xr[e]
                if sl.min() < 0:
                    continue
                ok = valid_stub_pairs(n, sl)
                for w in range(n):
                    aw = dist[w]
                    for x0 in range(n):
                        if not ok[w][x0]:
                            continue
                        d = aw[x0]
                        s = n - 1 - d
                        for (y, z) in M:
                            D = dist[y][z]
                            checked["se1"] += 1
                            if D > 2 * s:
                                fail(f"SE1 g6={line} M={M} w={w} x0={x0} "
                                     f"edge=({y},{z}) D={D} s={s}")
                            checked["se2"] += 1
                            if 2 * D > 2 * s + d:
                                fail(f"SE2 g6={line} M={M} w={w} x0={x0} "
                                     f"edge=({y},{z}) D={D} s={s} d={d}")
                        # per-geodesic checks
                        geos = geodesics_between(n, adj, dist, w, x0)
                        for P in geos:
                            Pset = set(P)
                            Fs = [v for v in range(n) if v not in Pset]
                            for (y, z) in M:
                                lo = min(aw[y], aw[z])
                                hi = max(aw[y], aw[z])
                                W = [j for j in range(1, d + 1)
                                     if lo < j <= hi]
                                checked["g1"] += 1
                                if W:
                                    chg = [f for f in Fs
                                           if min(W) - 1 <= aw[f] <= max(W)]
                                    if len(W) > 2 * len(chg):
                                        fail(f"G1 g6={line} M={M} w={w} "
                                             f"x0={x0} edge=({y},{z}) "
                                             f"|W|={len(W)} chg={len(chg)}")
                                checked["msl"] += 1
                                for k in range(1, d + 1):
                                    ek = tuple(sorted((P[k - 1], P[k])))
                                    if not same_comp_minus_edge(
                                            n, edges, ek, y, z):
                                        fail(f"MSL g6={line} M={M} w={w} "
                                             f"x0={x0} edge=({y},{z}) k={k}")
        print(f"n={n} done t={time.time()-t0:.0f}s "
              f"checked={checked}", flush=True)
    print(f"\nFAILURES: {FAIL}")
    sys.exit(1 if FAIL else 0)


if __name__ == "__main__":
    main()
