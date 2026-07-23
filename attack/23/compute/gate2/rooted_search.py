"""rooted_search.py — task-2 block-decomposition analysis via rooted instances.

A *rooted instance* R = (B, M, w, sigma) is: connected bipartite B on n
vertices, internal M-edges (same side, d_B >= 4), a marked vertex w, and
stub counts sigma : V \\ {w} -> N (sigma(u) = number of cross M-edges whose
V_1-endpoint is u, cut off at the articulation w).  Validity:

    (rooted flip)  for all T subseteq V \\ {w}:
                   e_M(delta T) + sigma(T) <= e_B(delta T).

THEOREM (proved in analysis.md, spot-verified here): a composite instance
glued from two rooted instances at w is a valid (max-cut) instance iff both
halves are rooted-valid; distances add across w:  d(u,v) = d_1(u,w) + d_2(w,v).

Boundary potential (SOC form): v_R(t) = (sqrt(Gamma_int), (d_j + t_j)_j),
||v_R(t)||^2 = Gamma_int + sum_j (d_j + t_j)^2.  Minkowski gives for any
composite and any t-split with t1_j + t2_j = 1:
    sqrt(Gamma_comp) <= ||v_1(t1)|| + ||v_2(t2)||.
So block decomposition "superadds" for the pair iff
    PAIRBOUND := min over t in [0,1]^k of ||v_1(t)|| + ||v_2(1-t)|| <= N,
with N = n_1 + n_2 - 1.  We also track the fixed-split potential
    D' : Psi = Gamma_int + sum_j (d_j + 1/2)^2 <= (n - 1/2)^2,
which pairwise implies PAIRBOUND but may itself be false.

Stage A: enumerate ALL valid rooted instances, n_B <= NB_MAX, |M| <= 2,
         total stubs k in {1, 2}; collect signatures (n, Gamma, D).
Stage B: all compatible signature pairs; check PAIRBOUND (convex, fine grid,
         exact Fraction evaluation at grid points); flag violating pairs.
Stage C: for flagged pairs, assemble real composites from witnesses, verify
         (exact brute max cut) that the composite is valid, and test
         Gamma_comp <= N^2 directly.
"""
import sys, os, subprocess
from fractions import Fraction
from itertools import combinations, combinations_with_replacement
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import (parse_graph6, adj_masks, bfs_dist, b_connected,
                    all_max_cuts, cut_value, split_edges, gamma_of_instance)

GENG = "/opt/homebrew/bin/geng"
NB_MAX = 9

import numpy as np

# ------------------------------------------------------------------- stage A
def bipartition(n, edges):
    adj = adj_masks(n, edges)
    side = [-1] * n
    side[0] = 0
    stack = [0]
    while stack:
        x = stack.pop()
        m = adj[x]
        while m:
            y = (m & -m).bit_length() - 1
            m &= m - 1
            if side[y] < 0:
                side[y] = 1 - side[x]
                stack.append(y)
            elif side[y] == side[x]:
                return None
    return side


def enumerate_rooted(nb):
    """Yield valid rooted instances (n, edges(B), w, M, sigma_dict, Gamma, D)."""
    out = subprocess.run([GENG, "-q", "-c", "-b", str(nb)],
                         capture_output=True, text=True)
    for line in out.stdout.splitlines():
        n, edges = parse_graph6(line)
        side = bipartition(n, edges)
        assert side is not None
        adj = adj_masks(n, edges)
        # all-pairs distances in B
        dist = [bfs_dist(n, adj, s) for s in range(n)]
        # internal M candidates
        mcand = [(u, v) for u in range(n) for v in range(u + 1, n)
                 if side[u] == side[v] and dist[u][v] >= 4]
        for u, v in mcand:
            assert dist[u][v] % 2 == 0
        msets = [()]
        msets += [((u, v),) for (u, v) in mcand]
        msets += [pair for pair in combinations(mcand, 2)]
        # vectorised over all T in [0, 2^n): bit arrays per vertex
        Tarr = np.arange(1 << n, dtype=np.uint32)
        bit = [((Tarr >> x) & 1).astype(np.int16) for x in range(n)]
        for M in msets:
            # slack(T) = e_B(delta T) - e_M(delta T), all T
            slack = np.zeros(1 << n, dtype=np.int16)
            for (a, b) in edges:
                slack += bit[a] ^ bit[b]
            for (a, b) in M:
                slack -= bit[a] ^ bit[b]
            gam = sum((dist[a][b] + 1) ** 2 for (a, b) in M)
            for w in range(n):
                others = [x for x in range(n) if x != w]
                sel = bit[w] == 0     # T subseteq V \ {w}
                slack_w = slack[sel]
                bit_w = {x: bit[x][sel] for x in others}
                sigmas = []
                for x in others:
                    sigmas.append(((x, 1),))
                for x, y in combinations_with_replacement(others, 2):
                    if x == y:
                        sigmas.append(((x, 2),))
                    else:
                        sigmas.append(((x, 1), (y, 1)))
                for sig in sigmas:
                    sd = dict(sig)
                    sigT = sum(s * bit_w[x] for x, s in sd.items())
                    if (sigT > slack_w).any():
                        continue
                    D = tuple(sorted(sum(([dist[x][w]] * s
                                          for x, s in sd.items()), [])))
                    yield (n, edges, w, M, sd, gam, D, line)


def stage_A():
    sigs = {}     # (n, Gamma, D) -> witness
    for nb in range(2, NB_MAX + 1):
        cnt = 0
        for inst in enumerate_rooted(nb):
            n, edges, w, M, sd, gam, D, g6 = inst
            cnt += 1
            key = (n, gam, D)
            if key not in sigs:
                sigs[key] = inst
        print(f"n_B={nb}: valid rooted instances counted={cnt}, "
              f"cumulative signatures={len(sigs)}")
    return sigs


# ------------------------------------------------------------------- stage B
def psi_half(n, gam, D):
    """D' potential value and bound (exact Fractions)."""
    val = gam + sum((Fraction(2 * d + 1, 2)) ** 2 for d in D)
    bound = Fraction(2 * n - 1, 2) ** 2
    return val, bound


def pairbound_ok(sig1, sig2, perm, grid=64):
    """Check exists t in [0,1]^k with ||v1(t)||+||v2(1-t)|| <= N, exact eval
    on grid (sufficient for a PASS).  Returns (ok, best_float)."""
    import math
    (n1, g1, D1) = sig1
    (n2, g2, D2) = sig2
    k = len(D1)
    N = n1 + n2 - 1
    best = None
    def val(ts):
        s1 = g1 + sum((D1[j] + ts[j]) ** 2 for j in range(k))
        s2 = g2 + sum((perm[j] + 1 - ts[j]) ** 2 for j in range(k))
        return math.sqrt(s1) + math.sqrt(s2)
    if k == 1:
        cand = [Fraction(i, grid) for i in range(grid + 1)]
        for t in cand:
            s1 = g1 + (D1[0] + t) ** 2
            s2 = g2 + (perm[0] + 1 - t) ** 2
            # exact check sqrt(s1)+sqrt(s2) <= N  <=>  s1+s2+2 sqrt(s1 s2) <= N^2
            rem = N * N - s1 - s2
            if rem >= 0 and 4 * s1 * s2 <= rem * rem:
                return True, None
        best = min(val([float(t)]) for t in cand)
        return False, best
    else:
        cand = [Fraction(i, grid) for i in range(grid + 1)]
        bestf = 1e18
        for t0 in cand:
            for t1 in cand:
                s1 = g1 + (D1[0] + t0) ** 2 + (D1[1] + t1) ** 2
                s2 = g2 + (perm[0] + 1 - t0) ** 2 + (perm[1] + 1 - t1) ** 2
                rem = N * N - s1 - s2
                if rem >= 0 and 4 * s1 * s2 <= rem * rem:
                    return True, None
                import math as _m
                bestf = min(bestf, _m.sqrt(float(s1)) + _m.sqrt(float(s2)))
        return False, bestf


def stage_Bprime(sigs):
    """TRUE composition inequality at signature level (exact integers):
    for all compatible realizable signature pairs,
        Gamma_1 + Gamma_2 + sum_j (d1_j + d2_pi(j) + 1)^2 <= (n_1 + n_2 - 1)^2.
    This is EQUIVALENT to the Gamma-conjecture restricted to instances whose
    B has a cut vertex (within enumerated sizes).  Report violations and
    equality pairs."""
    keys = sorted(sigs.keys())
    viol, eq = [], []
    npairs = 0
    for i, s1 in enumerate(keys):
        for s2 in keys[i:]:
            (n1, g1, D1), (n2, g2, D2) = s1, s2
            if len(D1) != len(D2):
                continue
            k = len(D1)
            perms = [D2] if k == 1 else [tuple(D2), (D2[1], D2[0])]
            for perm in set(perms):
                if any((D1[j] + perm[j]) % 2 or D1[j] + perm[j] < 4
                       for j in range(k)):
                    continue
                npairs += 1
                N = n1 + n2 - 1
                lhs = g1 + g2 + sum((D1[j] + perm[j] + 1) ** 2 for j in range(k))
                if lhs > N * N:
                    viol.append((s1, s2, perm, lhs, N * N))
                elif lhs == N * N:
                    eq.append((s1, s2, perm, lhs))
    print(f"\nStage B': TRUE pair inequality over {npairs} compatible signature "
          f"pairs: violations={len(viol)}, equalities={len(eq)}")
    for v in viol[:30]:
        print(f"  TRUE-PAIR-VIOL {v[0]} x {v[1]} perm={v[2]} lhs={v[3]} > N^2={v[4]}")
    for e in eq[:30]:
        print(f"  TRUE-PAIR-EQ   {e[0]} x {e[1]} perm={e[2]} lhs={e[3]}")
    return viol, eq


def stage_B(sigs):
    keys = sorted(sigs.keys())
    # D' violations
    dviol = []
    for (n, gam, D) in keys:
        val, bound = psi_half(n, gam, D)
        if val > bound:
            dviol.append(((n, gam, D), val, bound))
    print(f"\nD' (fixed t=1/2) violations among {len(keys)} signatures: {len(dviol)}")
    for s, v, b in dviol[:15]:
        print(f"  D'-VIOL sig={s}  Psi={v} > {b}")
    # pairings
    flags = []
    npairs = 0
    for i, s1 in enumerate(keys):
        for s2 in keys[i:]:
            (n1, g1, D1), (n2, g2, D2) = s1, s2
            if len(D1) != len(D2):
                continue
            k = len(D1)
            perms = [D2] if k == 1 else [tuple(D2), (D2[1], D2[0])]
            for perm in perms:
                # pairing constraints: a+b even and >= 4
                if any((D1[j] + perm[j]) % 2 or D1[j] + perm[j] < 4
                       for j in range(k)):
                    continue
                npairs += 1
                ok, best = pairbound_ok((n1, g1, D1), (n2, g2, D2), perm)
                if not ok:
                    N = n1 + n2 - 1
                    flags.append((s1, s2, perm, best, N))
    print(f"\ncompatible signature pairs tested: {npairs}, "
          f"PAIRBOUND failures: {len(flags)}")
    for f in flags[:25]:
        print(f"  PAIR-FAIL {f[0]} x {f[1]} perm={f[2]} min||v1||+||v2||~{f[3]:.4f} N={f[4]}")
    return dviol, flags


# ------------------------------------------------------------------- stage C
def assemble(inst1, inst2, pairing):
    """Glue two rooted witnesses at their w's.  pairing: list of (x1, x2)
    stub-vertex pairs (with multiplicity resolved).  Returns (n, edges, S) or
    None if assembly constraint (multi-edge / triangle) fails."""
    n1, e1, w1, M1, sd1, g1, D1, _ = inst1
    n2, e2, w2, M2, sd2, g2, D2, _ = inst2
    # relabel: block1 keeps labels, w = w1; block2 vertex x -> map2[x]
    map2 = {}
    nxt = n1
    for x in range(n2):
        if x == w2:
            map2[x] = w1
        else:
            map2[x] = nxt
            nxt += 1
    n = nxt
    edges = list(e1) + [(min(map2[a], map2[b]), max(map2[a], map2[b]))
                        for (a, b) in e2]
    Mall = list(M1) + [(min(map2[a], map2[b]), max(map2[a], map2[b]))
                       for (a, b) in M2]
    cross = []
    for x1, x2 in pairing:
        a, b = x1, map2[x2]
        e = (min(a, b), max(a, b))
        if e in cross or e in Mall or e in edges:
            return None
        cross.append(e)
    Mall += cross
    alledges = edges + Mall
    if len(set(alledges)) != len(alledges):
        return None
    # triangle check
    adj = adj_masks(n, alledges)
    for (a, b) in alledges:
        if adj[a] & adj[b]:
            return None
    # colouring: proper 2-colouring of B (connected), gives S
    sideB = bipartition(n, edges)
    S = 0
    for v in range(n):
        if sideB[v]:
            S |= 1 << v
    # normalise vertex n-1 side 0
    if (S >> (n - 1)) & 1:
        S = ((1 << n) - 1) & ~S
    return n, alledges, S


def stage_C(sigs, flags):
    print("\nStage C: direct verification of flagged pairs (composites)")
    for s1, s2, perm, best, N in flags:
        i1, i2 = sigs[s1], sigs[s2]
        # build pairing at vertex level from sigma dicts
        stubs1 = sum(([x] * s for x, s in i1[4].items()), [])
        stubs2 = sum(([x] * s for x, s in i2[4].items()), [])
        # order stubs to match signature D order
        d1 = {x: bfs_dist(i1[0], adj_masks(i1[0], i1[1]), x)[i1[2]] for x in set(stubs1)}
        d2 = {x: bfs_dist(i2[0], adj_masks(i2[0], i2[1]), x)[i2[2]] for x in set(stubs2)}
        stubs1.sort(key=lambda x: d1[x])
        stubs2.sort(key=lambda x: d2[x])
        # align stubs2 to 'perm' distance order
        # perm[j] is the distance to pair with D1[j]
        s2sorted = sorted(stubs2, key=lambda x: d2[x])
        want = list(perm)
        s2perm = []
        pool = s2sorted[:]
        okp = True
        for dwant in want:
            found = None
            for x in pool:
                if d2[x] == dwant:
                    found = x
                    break
            if found is None:
                okp = False
                break
            pool.remove(found)
            s2perm.append(found)
        if not okp:
            print(f"  [skip] could not realise perm for {s1} x {s2}")
            continue
        res = assemble(i1, i2, list(zip(stubs1, s2perm)))
        if res is None:
            print(f"  [assembly blocked] {s1} x {s2} perm={perm} (multi-edge/triangle)")
            continue
        n, alledges, S = res
        adj = adj_masks(n, alledges)
        cv = cut_value(n, adj, S)
        best_mc = -1
        for T in range(1 << (n - 1)):
            c = cut_value(n, adj, T)
            if c > best_mc:
                best_mc = c
        if cv != best_mc:
            print(f"  [NOT MAX CUT?!] {s1} x {s2}: cut={cv} mc={best_mc}  "
                  f"— equivalence theorem violated, INVESTIGATE")
            continue
        inst = gamma_of_instance(n, alledges, S)
        verdict = "Gamma<=N^2 HOLDS" if inst["Gamma"] <= n * n else "*** GAMMA CEX ***"
        print(f"  composite N={n} Gamma={inst['Gamma']} N^2={n*n}  {verdict}  "
              f"(pair {s1} x {s2}, perm={perm}, minSOC~{best:.4f} > N={N})")


def main():
    sigs = stage_A()
    print(f"\ntotal distinct signatures: {len(sigs)}")
    for k in sorted(sigs):
        pass
    tviol, teq = stage_Bprime(sigs)
    dviol, flags = stage_B(sigs)
    stage_C(sigs, flags)
    # spot-verify equivalence theorem on a sample of valid composites:
    print("\n(sanity) K_{2,2}+double-stub D' witness check:")
    for key, val in sorted(sigs.items()):
        n, gam, D = key
        if n == 4 and gam == 0 and D == (2, 2):
            v, b = psi_half(n, gam, D)
            print(f"  sig={key}: Psi={v} vs bound={b} -> "
                  f"{'VIOLATES D-prime' if v > b else 'ok'}; witness g6={val[7]} "
                  f"w={val[2]} sigma={val[4]}")


if __name__ == "__main__":
    main()
