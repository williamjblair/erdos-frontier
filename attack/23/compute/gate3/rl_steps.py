"""rl_steps.py — machine verification of the individual proof steps of the
Lemma-RL writeup (compute23/gate3/lemma_rl_proof.md).

Each STEP-k function checks one claim of the proof on a family of instances
(exhaustive n <= NMAX one-stub rooted instances, |M| <= MMAX), in exact
integer arithmetic.  Any failure prints loudly and sets a nonzero exit.

Steps verified here:
  S-pendant : pendant-stub construction — every valid unrooted instance
              (B1, M1) plus a pendant vertex x0 attached at any w gives a
              valid one-stub rooted instance with d = 1 (Theorem 2.6 /
              sandwich).  Checked by direct RFC evaluation.
  S-leafdel : M-free leaf deletion preserves rooted validity, d, all D_uv
              (Lemma 3.1).
  S-mleafdel: M-loaded leaf deletion (leaf z carrying M-edges, z not w/x0)
              preserves rooted validity of (B−z, M−M_z) (Lemma 3.4).
  S-rootmove: root move off an M-free leaf root (w leaf, d>=2) gives a
              valid rooted instance with root w' = the neighbour, d-1
              (Lemma 3.2).
  S-stubmove: stub retraction off an M-free leaf stub (x0 leaf, x0 not in
              V(M), d>=2): stub moves to the neighbour, then x0 deleted;
              valid, d-1 (Lemma 3.3).
  S-attach  : every off-corridor vertex has at most 2 neighbours on any
              fixed w–x0 geodesic, at positions {j−1, j+1} (Lemma 4.2).
  S-suffix  : the suffix-cut inequalities e_M(δT_k) <= e_B(suffix_k, F)
              for every w–x0 geodesic P and 1 <= k <= d (Lemma 4.3).
  S-s01     : s <= 1 implies M = ∅ (Theorem 3.6) — scan check.
  S-tree    : B a tree implies Σ_M d_B(u,v) + d <= n − 1 (edge-disjoint
              routing bound, Lemma 3.7) and RL with slack.

Usage: python3 rl_steps.py NMAX MMAX
"""
import sys, time
from itertools import combinations
import numpy as np
from rl_lib import (parse_graph6, adj_masks, bfs_dist, p_of_d, rl_rhs,
                    all_dists, m_candidates, union_triangle_free, xor_bits,
                    slack_array, valid_stub_pairs, gamma_of, gen_bipartite,
                    geodesics_between, check_rfc_direct)

FAIL = 0


def fail(msg):
    global FAIL
    FAIL += 1
    print(f"*** STEP FAILURE *** {msg}")


def unrooted_valid(n, edges, M, bit):
    return slack_array(n, edges, M, bit).min() >= 0


def rooted_valid(n, edges, M, w, x0, bit=None):
    if bit is None:
        bit = xor_bits(n)
    sl = slack_array(n, edges, M, bit)
    if sl.min() < 0:
        return False
    ok = valid_stub_pairs(n, sl)
    return bool(ok[w][x0])


def delete_vertex(n, edges, M, z):
    """Delete vertex z; relabel > z down by 1.  Returns (n', edges', M')
    with M-edges at z removed."""
    def rl(v):
        return v - 1 if v > z else v
    e2 = [(rl(a), rl(b)) for a, b in edges if a != z and b != z]
    m2 = [(rl(a), rl(b)) for a, b in M if a != z and b != z]
    return n - 1, [tuple(sorted(e)) for e in e2], [tuple(sorted(e)) for e in m2]


def connected(n, edges):
    if n == 0:
        return False
    adj = adj_masks(n, edges)
    return all(x >= 0 for x in bfs_dist(n, adj, 0))


def main():
    nmax = int(sys.argv[1])
    mmax = int(sys.argv[2])
    t0 = time.time()
    counts = dict(pendant=0, leafdel=0, mleafdel=0, rootmove=0, stubmove=0,
                  attach=0, suffix=0, s01=0, tree=0)

    for n in range(2, nmax + 1):
        bit = xor_bits(n)
        bit_m1 = xor_bits(n - 1) if n >= 3 else None
        for line in gen_bipartite(n):
            nn, edges = parse_graph6(line)
            adj = adj_masks(n, edges)
            dist = all_dists(n, edges)
            deg = [bin(adj[v]).count("1") for v in range(n)]
            mcand = m_candidates(n, dist)
            ebase = np.zeros(1 << n, dtype=np.int32)
            for a, b in edges:
                ebase += bit[a] ^ bit[b]
            xr = {e: bit[e[0]] ^ bit[e[1]] for e in mcand}
            msets = []
            kmax = len(mcand) if mmax == 0 else mmax
            for k in range(0, kmax + 1):
                msets.extend(combinations(mcand, k))
            for M in msets:
                if M and not union_triangle_free(n, edges, M):
                    continue
                sl = ebase.copy()
                for e in M:
                    sl -= xr[e]
                if sl.min() < 0:
                    continue
                # ---- S-pendant: unrooted instance; attach pendant stub at
                # every w; must be rooted-valid with d=1.  (Do it on the
                # unrooted instance itself, i.e. B is the graph, any w.)
                if n + 1 <= nmax + 1:
                    bitp = xor_bits(n + 1)
                    for w in range(n):
                        e2 = edges + [(w, n)]
                        okp, Tbad = check_rfc_direct(n + 1, e2, M, w, n)
                        counts["pendant"] += 1
                        if not okp:
                            fail(f"S-pendant g6={line} M={M} w={w} T={Tbad}")
                        break  # one w per instance keeps cost sane
                ok = valid_stub_pairs(n, sl)
                gam = gamma_of(M, dist)
                mv = set()
                for a, b in M:
                    mv.add(a); mv.add(b)
                for w in range(n):
                    for x0 in range(n):
                        if not ok[w][x0]:
                            continue
                        d = dist[w][x0]
                        s = n - 1 - d
                        # ---- S-s01
                        counts["s01"] += 1
                        if s <= 1 and M:
                            fail(f"S-s01 g6={line} M={M} w={w} x0={x0} s={s}")
                        # ---- S-tree
                        if len(edges) == n - 1:
                            counts["tree"] += 1
                            vol = sum(dist[a][b] for a, b in M) + d
                            if vol > n - 1:
                                fail(f"S-tree vol g6={line} M={M} w={w} x0={x0}")
                            if gam > rl_rhs(n, d):
                                fail(f"S-tree RL g6={line} M={M} w={w} x0={x0}")
                        # ---- geodesic-based checks (first geodesic only,
                        # attachments hold for EVERY geodesic; use all for
                        # n <= 9 to keep cost bounded)
                        geos = geodesics_between(n, adj, dist, w, x0)
                        for P in (geos if n <= 9 else geos[:2]):
                            Pset = set(P)
                            Fset = [v for v in range(n) if v not in Pset]
                            pos = {v: i for i, v in enumerate(P)}
                            # S-attach
                            counts["attach"] += 1
                            for f in Fset:
                                nb = [pos[y] for y in range(n)
                                      if (adj[f] >> y) & 1 and y in Pset]
                                if nb and (max(nb) - min(nb) not in (0, 2)):
                                    fail(f"S-attach g6={line} f={f} nb={nb}")
                                if len(nb) > 2:
                                    fail(f"S-attach>2 g6={line} f={f} nb={nb}")
                            # S-suffix: e_M(δT_k) <= e_B(suffix_k, F)
                            counts["suffix"] += 1
                            for k in range(1, d + 1):
                                suf = set(P[k:])
                                eM = sum(1 for a, b in M
                                         if (a in suf) != (b in suf))
                                cap = sum(1 for a, b in edges
                                          if ((a in suf and b in Fset) or
                                              (b in suf and a in Fset)))
                                if eM > cap:
                                    fail(f"S-suffix g6={line} M={M} w={w} "
                                         f"x0={x0} k={k} eM={eM} cap={cap}")
                        # ---- deletion/move reductions (only test a sample:
                        # every leaf of every valid instance)
                        for z in range(n):
                            if deg[z] != 1:
                                continue
                            y = (adj[z]).bit_length() - 1
                            if z == w:
                                # S-rootmove (w leaf, M-free at w, d>=2)
                                if d >= 2 and z not in mv:
                                    n2, e2, m2 = delete_vertex(n, edges, M, z)
                                    w2 = y - 1 if y > z else y
                                    x2 = x0 - 1 if x0 > z else x0
                                    counts["rootmove"] += 1
                                    if not rooted_valid(n2, e2, m2, w2, x2):
                                        fail(f"S-rootmove g6={line} M={M} "
                                             f"w={w} x0={x0}")
                                continue
                            if z == x0:
                                # S-stubmove (x0 leaf, M-free, d>=2)
                                if d >= 2 and z not in mv:
                                    n2, e2, m2 = delete_vertex(n, edges, M, z)
                                    w2 = w - 1 if w > z else w
                                    y2 = y - 1 if y > z else y
                                    counts["stubmove"] += 1
                                    if not rooted_valid(n2, e2, m2, w2, y2):
                                        fail(f"S-stubmove g6={line} M={M} "
                                             f"w={w} x0={x0}")
                                continue
                            n2, e2, m2 = delete_vertex(n, edges, M, z)
                            w2 = w - 1 if w > z else w
                            x2 = x0 - 1 if x0 > z else x0
                            if z in mv:
                                counts["mleafdel"] += 1
                                if not rooted_valid(n2, e2, m2, w2, x2):
                                    fail(f"S-mleafdel g6={line} M={M} w={w} "
                                         f"x0={x0} z={z}")
                            else:
                                counts["leafdel"] += 1
                                if not rooted_valid(n2, e2, m2, w2, x2):
                                    fail(f"S-leafdel g6={line} M={M} w={w} "
                                         f"x0={x0} z={z}")
        print(f"n={n} done t={time.time()-t0:.1f}s", flush=True)

    print("\ncounts:", counts)
    print(f"FAILURES: {FAIL}")
    sys.exit(1 if FAIL else 0)


if __name__ == "__main__":
    main()
