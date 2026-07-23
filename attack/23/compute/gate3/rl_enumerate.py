"""rl_enumerate.py — exhaustive verification of Lemma RL on one-stub rooted
instances.

Usage:  python3 rl_enumerate.py NMAX MMAX [tri]
  NMAX  : enumerate connected bipartite B on 2..NMAX vertices (geng)
  MMAX  : |M| <= MMAX  (0 = unbounded, all subsets of the candidate set)
  tri   : if present, require B ∪ M triangle-free (the RL hypothesis);
          otherwise enumerate the superset without the check (matches gate2).

Outputs: signature table (n, Γ, d) with RL slack, count of instances,
minimal-slack witnesses per (d, s), and any RL violation (loudly).
Exact integer arithmetic throughout.
"""
import sys, time
from itertools import combinations
import numpy as np
from rl_lib import (p_of_d, rl_rhs, all_dists, m_candidates,
                    union_triangle_free, xor_bits, slack_array,
                    valid_stub_pairs, gamma_of, gen_bipartite)


def m_subsets(mcand, mmax):
    if mmax == 0:
        mmax = len(mcand)
    for k in range(0, mmax + 1):
        for M in combinations(mcand, k):
            yield M


def main():
    nmax = int(sys.argv[1])
    mmax = int(sys.argv[2])
    tri = len(sys.argv) > 3 and sys.argv[3] == "tri"
    t0 = time.time()
    sigs = {}          # (n, gam, d) -> (min_slack, witness, count)
    minslack_ds = {}   # (d, s) -> (slack, witness)   only Γ>0 entries
    violations = []
    total_valid = 0

    for n in range(2, nmax + 1):
        bit = xor_bits(n)
        cnt_n = 0
        for line in gen_bipartite(n):
            from rl_lib import parse_graph6
            nn, edges = parse_graph6(line)
            assert nn == n
            dist = all_dists(n, edges)
            mcand = m_candidates(n, dist)
            ebase = np.zeros(1 << n, dtype=np.int32)
            for a, b in edges:
                ebase += bit[a] ^ bit[b]
            xr = {e: bit[e[0]] ^ bit[e[1]] for e in mcand}
            for M in m_subsets(mcand, mmax):
                if M and tri and not union_triangle_free(n, edges, M):
                    continue
                sl = ebase.copy()
                for e in M:
                    sl -= xr[e]
                if sl.min() < 0:
                    continue          # unrooted S2 fails: no valid rooting
                gam = gamma_of(M, dist)
                ok = valid_stub_pairs(n, sl)
                for w in range(n):
                    for x0 in range(n):
                        if not ok[w][x0]:
                            continue
                        d = dist[w][x0]
                        s = n - 1 - d
                        rhs = rl_rhs(n, d)
                        slack = rhs - gam
                        cnt_n += 1
                        total_valid += 1
                        key = (n, gam, d)
                        wit = (line, edges, M, w, x0)
                        if key not in sigs or slack < sigs[key][0]:
                            c = sigs.get(key, (0, None, 0))[2]
                            sigs[key] = (slack, wit, c + 1)
                        else:
                            a, b, c = sigs[key]
                            sigs[key] = (a, b, c + 1)
                        if slack < 0:
                            violations.append((key, wit))
                            print(f"*** RL VIOLATION *** {key} g6={line} "
                                  f"M={M} w={w} x0={x0} Γ={gam} rhs={rhs}")
                        if gam > 0:
                            k2 = (d, s)
                            if k2 not in minslack_ds or slack < minslack_ds[k2][0]:
                                minslack_ds[k2] = (slack, key, wit)
        print(f"n={n}: valid one-stub instances={cnt_n}, "
              f"cum sigs={len(sigs)}, t={time.time()-t0:.1f}s", flush=True)

    print(f"\nTOTAL valid one-stub instances: {total_valid}")
    print(f"distinct signatures (n, Γ, d): {len(sigs)}")
    print(f"RL violations: {len(violations)}")

    print("\n--- signature table (n, Γ, d) : s, rhs, slack, count ---")
    for key in sorted(sigs):
        n, gam, d = key
        s = n - 1 - d
        rhs = rl_rhs(n, d)
        slack, wit, c = sigs[key]
        tag = " TIGHT" if slack == 0 else ""
        print(f"  ({n:2d}, {gam:3d}, {d:2d})  s={s}  rhs={rhs:3d}  "
              f"slack={slack:3d}  count={c}{tag}")

    print("\n--- minimal slack per (d, s), Γ>0 only ---")
    for k2 in sorted(minslack_ds):
        slack, key, wit = minslack_ds[k2]
        line, edges, M, w, x0 = wit
        print(f"  d={k2[0]} s={k2[1]}: slack={slack} sig={key} g6={line} "
              f"M={M} w={w} x0={x0}")

    # nonzero-Γ signature count restricted report
    nz = [k for k in sigs if k[1] > 0]
    print(f"\nsignatures with Γ>0: {len(nz)}; with Γ=0: {len(sigs)-len(nz)}")


if __name__ == "__main__":
    main()
