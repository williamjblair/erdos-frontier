"""rl_corridor.py — targeted exhaustive search in the thin-corridor regime.

Fix d and s <= 3.  B = corridor P = u_0..u_d (w = u_0, x0 = u_d) plus s
off-corridor vertices f_i.  Each f attaches to P on a set S ⊆ {a} or
{a, a+2} (the only geodesic-preserving patterns), F–F edges optional
(bipartite-consistent), connectivity and dist(w, x0) = d enforced, then all
M-sets with |M| <= MMAX (B ∪ M triangle-free), RFC checked exactly, and the
maximal Γ per (d, s) compared with the RL bound s(2d+2+s) + 2s·p(d).

This probes RL far beyond the n <= 11 global enumeration, exactly where the
bound is thinnest.  Usage: python3 rl_corridor.py D_MIN D_MAX S MMAX
"""
import sys, time
from itertools import combinations, product
import numpy as np
from rl_lib import (adj_masks, bfs_dist, p_of_d, rl_rhs, all_dists,
                    m_candidates, union_triangle_free, xor_bits,
                    slack_array, valid_stub_pairs, gamma_of)


def attach_options(d):
    """All (frozenset of corridor positions) an F-vertex may attach to:
    {} (attach via F only), {a}, or {a, a+2}."""
    opts = [frozenset()]
    opts += [frozenset([a]) for a in range(d + 1)]
    opts += [frozenset([a, a + 2]) for a in range(d - 1)]
    return opts


def side_of(S, d):
    """Bipartition side of an F-vertex given corridor attachment positions
    (side of u_j = j mod 2; f attaches to side (a mod 2), so f is on side
    (a+1) mod 2).  None if unattached (side free)."""
    if not S:
        return None
    a = min(S)
    return (a + 1) % 2


def main():
    dmin, dmax, s, mmax = map(int, sys.argv[1:5])
    t0 = time.time()
    for d in range(dmin, dmax + 1):
        n = d + 1 + s
        bit = xor_bits(n)
        rhs = rl_rhs(n, d)
        best = (-1, None)
        seen = set()
        opts = attach_options(d)
        nconf = 0
        # F vertices are u indices d+1 .. d+s
        for atts in combinations(product(opts, repeat=1), 0) or [()]:
            pass
        for atts in product(opts, repeat=s):
            # F-F edge patterns
            for ffbits in range(1 << (s * (s - 1) // 2)):
                ffe = []
                k = 0
                okff = True
                for i in range(s):
                    for j in range(i + 1, s):
                        if (ffbits >> k) & 1:
                            ffe.append((i, j))
                        k += 1
                edges = [(i, i + 1) for i in range(d)]
                for i, S in enumerate(atts):
                    for a in list(atts[i]):
                        edges.append(tuple(sorted((a, d + 1 + i))))
                for i, j in ffe:
                    edges.append((d + 1 + i, d + 1 + j))
                # bipartite check via sides
                side = [k % 2 for k in range(d + 1)] + [None] * s
                for i, S in enumerate(atts):
                    side[d + 1 + i] = side_of(S, d)
                # propagate through F-F edges (2-colour); reject conflicts
                changed = True
                bad = False
                while changed and not bad:
                    changed = False
                    for i, j in ffe:
                        a, b = side[d + 1 + i], side[d + 1 + j]
                        if a is None and b is not None:
                            side[d + 1 + i] = 1 - b; changed = True
                        elif b is None and a is not None:
                            side[d + 1 + j] = 1 - a; changed = True
                        elif a is not None and a == b:
                            bad = True
                if bad:
                    continue
                if any(x is None for x in side):
                    continue  # disconnected F-vertex with no anchor
                adj = adj_masks(n, edges)
                dist0 = bfs_dist(n, adj, 0)
                if any(x < 0 for x in dist0):
                    continue  # disconnected
                if dist0[d] != d:
                    continue  # corridor no longer geodesic
                key = tuple(sorted(edges))
                if key in seen:
                    continue
                seen.add(key)
                nconf += 1
                dist = all_dists(n, edges)
                mcand = m_candidates(n, dist)
                ebase = np.zeros(1 << n, dtype=np.int32)
                for a, b in edges:
                    ebase += bit[a] ^ bit[b]
                xr = {e: bit[e[0]] ^ bit[e[1]] for e in mcand}
                kmax = len(mcand) if mmax == 0 else mmax
                msets = []
                for k in range(1, kmax + 1):
                    msets.extend(combinations(mcand, k))
                for M in msets:
                    if not union_triangle_free(n, edges, M):
                        continue
                    sl = ebase.copy()
                    for e in M:
                        sl -= xr[e]
                    if sl.min() < 0:
                        continue
                    ok = valid_stub_pairs(n, sl)
                    if not ok[0][d]:
                        continue
                    gam = gamma_of(M, dist)
                    if gam > best[0]:
                        best = (gam, (edges, M))
                    if gam > rhs:
                        print(f"*** RL VIOLATION *** d={d} s={s} "
                              f"edges={edges} M={M} Γ={gam} rhs={rhs}")
        g, wit = best
        extra = ""
        if wit:
            Ds = sorted(all_dists(n, wit[0])[a][b] for a, b in wit[1])
            extra = f"  bestM={wit[1]} D's={Ds}"
        print(f"d={d} s={s} n={n}: configs={nconf} maxΓ={g} rhs={rhs} "
              f"slack={rhs - g if g >= 0 else 'NA'}{extra} "
              f"t={time.time()-t0:.0f}s", flush=True)


if __name__ == "__main__":
    main()
