"""rl_m1_frontier.py — mine the |M| = 1 feasibility frontier.

Enumerate all valid one-stub rooted instances with exactly one M-edge,
n <= NMAX; record which triples (d, s, D) are realizable, and for each
realizable (s, D) the minimal d.  This is the raw material for the
single-edge sub-lemma of the RL proof.

Usage: python3 rl_m1_frontier.py NMAX
"""
import sys, time
import numpy as np
from rl_lib import (parse_graph6, p_of_d, rl_rhs, all_dists, m_candidates,
                    xor_bits, valid_stub_pairs, gen_bipartite)


def main():
    nmax = int(sys.argv[1])
    t0 = time.time()
    tri = {}   # (d, s, D) -> witness
    for n in range(2, nmax + 1):
        bit = xor_bits(n)
        for line in gen_bipartite(n):
            nn, edges = parse_graph6(line)
            dist = all_dists(n, edges)
            mcand = m_candidates(n, dist)
            if not mcand:
                continue
            ebase = np.zeros(1 << n, dtype=np.int32)
            for a, b in edges:
                ebase += bit[a] ^ bit[b]
            for e in mcand:
                sl = ebase - (bit[e[0]] ^ bit[e[1]])
                if sl.min() < 0:
                    continue
                ok = valid_stub_pairs(n, sl)
                D = dist[e[0]][e[1]]
                for w in range(n):
                    for x0 in range(n):
                        if ok[w][x0]:
                            d = dist[w][x0]
                            key = (d, n - 1 - d, D)
                            if key not in tri:
                                tri[key] = (line, e, w, x0)
        print(f"n={n} done, triples={len(tri)}, t={time.time()-t0:.0f}s",
              flush=True)

    print("\nrealizable (d, s, D) with |M|=1, n <=", nmax)
    byD = {}
    for (d, s, D) in sorted(tri):
        byD.setdefault(D, []).append((d, s))
    for D in sorted(byD):
        print(f"  D={D}:")
        bys = {}
        for d, s in byD[D]:
            bys.setdefault(s, []).append(d)
        for s in sorted(bys):
            print(f"    s={s}: d in {sorted(bys[s])}")
    # frontier: for each (s, D) the min d
    print("\nmin d for each (s, D):")
    md = {}
    for (d, s, D) in tri:
        if (s, D) not in md or d < md[(s, D)]:
            md[(s, D)] = d
    for (s, D) in sorted(md):
        lhs = (D + 1) ** 2
        d = md[(s, D)]
        rhs = s * (2 * d + 2 + s) + 2 * s * p_of_d(d)
        print(f"  s={s} D={D}: min d={d}   [(D+1)^2={lhs} vs rhs at min d={rhs}]")


if __name__ == "__main__":
    main()
