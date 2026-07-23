"""rl_misc_checks.py — machine verification of the foundational claims of
lemma_rl_proof.md that are not covered by rl_steps.py / rl_se_verify.py.

  C1 (composite equivalence, Prop 2.4): for one witness of every one-stub
     signature (n <= NMAX, |M| <= 2), glue the minimal path partner
     (length p(d)) at w with crossing edge {x0, tip}: the composite must
     (a) satisfy the full unrooted flip condition S2 (all 2^N subsets),
     (b) be triangle-free with connected spanning cut graph,
     (c) have Γ̂ = Γ_int + (d+p+1)²  — so RL ⟺ Γ̂ <= N² exactly.
  C2 (symmetric RFC, Lemma 2.2): RFC  ⟺  ∀T ⊆ V: e_M(δT) + [T separates
     w, x0] <= e_B(δT).  Exhaustive n <= 7, all M, all (w,x0).
  C3 (RHS identity): s(2d+2+s) + 2sp = n² − (d+1)² + 2sp = s(s+2(d+p+1)),
     integer check over 1 <= d <= 60, 0 <= s <= 60.
  C4 (SE ⟹ RL algebra, Thm 6.2): for all 1 <= d <= 80, 1 <= s <= 80,
     4 <= D even with D <= 2s and 2D <= 2s + d:  (D+1)² <= rhs(d, s).

Usage: python3 rl_misc_checks.py NMAX
"""
import sys
from itertools import combinations
import numpy as np
from rl_lib import (parse_graph6, adj_masks, bfs_dist, p_of_d, rl_rhs,
                    all_dists, m_candidates, union_triangle_free, xor_bits,
                    slack_array, valid_stub_pairs, gamma_of, gen_bipartite,
                    check_rfc_direct)

FAIL = 0


def fail(msg):
    global FAIL
    FAIL += 1
    print(f"*** MISC FAILURE *** {msg}")


def unrooted_s2(n, edges, M):
    for T in range(1 << (n - 1)):        # complement symmetry
        eB = sum(1 for a, b in edges if ((T >> a) & 1) != ((T >> b) & 1))
        eM = sum(1 for a, b in M if ((T >> a) & 1) != ((T >> b) & 1))
        if eM > eB:
            return False
    return True


def check_C1(nmax):
    sigs = {}
    for n in range(2, nmax + 1):
        bit = xor_bits(n)
        for line in gen_bipartite(n):
            nn, edges = parse_graph6(line)
            dist = all_dists(n, edges)
            mcand = m_candidates(n, dist)
            msets = [()]
            msets += [(e,) for e in mcand] + list(combinations(mcand, 2))
            for M in msets:
                if M and not union_triangle_free(n, edges, M):
                    continue
                sl = slack_array(n, edges, M, bit)
                if sl.min() < 0:
                    continue
                ok = valid_stub_pairs(n, sl)
                gam = gamma_of(M, dist)
                for w in range(n):
                    for x0 in range(n):
                        if ok[w][x0]:
                            key = (n, gam, dist[w][x0])
                            if key not in sigs:
                                sigs[key] = (n, edges, M, w, x0)
    print(f"C1: gluing minimal partner for {len(sigs)} signature witnesses")
    for key, (n, edges, M, w, x0) in sorted(sigs.items()):
        d = key[2]
        p = p_of_d(d)
        # composite: path w = y_0 .. y_p (new vertices n .. n+p-1)
        N = n + p
        e2 = list(edges)
        prev = w
        for i in range(p):
            e2.append((min(prev, n + i), max(prev, n + i)))
            prev = n + i
        tip = prev
        M2 = list(M) + [(min(x0, tip), max(x0, tip))]
        # (b) triangle-free of B̂ ∪ M̂
        if not union_triangle_free(N, e2, M2):
            fail(f"C1-tri {key}")
            continue
        adj2 = adj_masks(N, e2)
        if any(x < 0 for x in bfs_dist(N, adj2, 0)):
            fail(f"C1-conn {key}")
            continue
        # (a) full unrooted S2
        if not unrooted_s2(N, e2, M2):
            fail(f"C1-S2 {key} n={n} M={M} w={w} x0={x0}")
            continue
        # (c) Γ̂ identity
        dist2 = all_dists(N, e2)
        gam2 = gamma_of(M2, dist2)
        want = key[1] + (d + p + 1) ** 2
        if gam2 != want:
            fail(f"C1-Γ {key}: got {gam2} want {want}")
        if gam2 > N * N and rl_rhs(n, d) >= key[1]:
            fail(f"C1-consistency {key}")
    print("C1 done")


def check_C2(nmax=7):
    cnt = 0
    for n in range(2, nmax + 1):
        bit = xor_bits(n)
        for line in gen_bipartite(n):
            nn, edges = parse_graph6(line)
            dist = all_dists(n, edges)
            mcand = m_candidates(n, dist)
            msets = [()] + [(e,) for e in mcand] + \
                list(combinations(mcand, 2))
            for M in msets:
                sl = slack_array(n, edges, M, bit)
                if sl.min() < 0:
                    continue
                ok = valid_stub_pairs(n, sl)
                for w in range(n):
                    for x0 in range(n):
                        if w == x0:
                            continue
                        rfc = bool(ok[w][x0])
                        # symmetric form over ALL T
                        sym = True
                        for T in range(1 << n):
                            eB = sum(1 for a, b in edges
                                     if ((T >> a) & 1) != ((T >> b) & 1))
                            eM = sum(1 for a, b in M
                                     if ((T >> a) & 1) != ((T >> b) & 1))
                            sep = ((T >> w) & 1) != ((T >> x0) & 1)
                            if eM + (1 if sep else 0) > eB:
                                sym = False
                                break
                        if rfc != sym:
                            fail(f"C2 g6={line} M={M} w={w} x0={x0} "
                                 f"rfc={rfc} sym={sym}")
                        cnt += 1
    print(f"C2 done ({cnt} comparisons)")


def check_C3():
    for d in range(1, 61):
        p = p_of_d(d)
        for s in range(0, 61):
            n = d + 1 + s
            a = s * (2 * d + 2 + s) + 2 * s * p
            b = n * n - (d + 1) ** 2 + 2 * s * p
            c = s * (s + 2 * (d + p + 1))
            if not (a == b == c):
                fail(f"C3 d={d} s={s}: {a} {b} {c}")
    print("C3 done")


def check_C4():
    bad = 0
    for d in range(1, 81):
        p = p_of_d(d)
        for s in range(1, 81):
            rhs = s * (2 * d + 2 + s) + 2 * s * p
            for D in range(4, min(2 * s, (2 * s + d) // 2) + 1, 2):
                if (D + 1) ** 2 > rhs:
                    fail(f"C4 d={d} s={s} D={D}")
                    bad += 1
    print("C4 done")


if __name__ == "__main__":
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    check_C3()
    check_C4()
    check_C2(7)
    check_C1(nmax)
    print(f"FAILURES: {FAIL}")
    sys.exit(1 if FAIL else 0)
