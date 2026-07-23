"""candidates.py — candidate-lemma search (task 3) over all valid instances.

Instances: dump files from gamma_search (graph6 + colouring bitmask), i.e.
ALL (connected triangle-free G, maximum cut) pairs with M != 0 for n <= 10,
near-tight ones for n = 11..13, plus injected big tight instances
(C_5[3], C_5[4], C_7[2]).

Candidate C3 (local load, full-strength L^2 form):
    exists a fractional routing lambda of every M-edge uv over its shortest
    B-paths (unit mass each) such that for every vertex x
        g(x) := sum_{uv} (l_uv+1) * lambda(paths through x)  <=  N.
    Since every shortest path has exactly l+1 vertices, sum_x g(x) = Gamma
    identically, so C3  ==>  Gamma <= N^2.
    Test: (a) uniform routing, exact Fractions;  (b) hub kill certificate
    (exact integers): L(x) = sum over M-edges whose EVERY shortest path
    contains x of (l+1); L(x) > N kills C3;  (c) LP min-max-load (float),
    with exact rational re-verification of the verdict.

Candidate C2 (path packing, L^1 form):
    M routable in B as a multicommodity flow with edge congestion <= 1.
    Test: (a) uniform shortest-path flow, exact edge loads <= 1;
    (b) edge-flow LP feasibility (float, min total capacity excess);
    kills exact-verified via rationalized Farkas certificate.

All KILL claims are exact; float only ever used to *find* certificates.
"""
import sys, os
from fractions import Fraction
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import (parse_graph6, split_edges, adj_masks, sp_counts,
                    c5_blowup, cycle, blowup, cut_value, max_cut_value,
                    gamma_of_instance)

try:
    import numpy as np
    from scipy.optimize import linprog
    HAVE_SCIPY = True
except Exception:
    HAVE_SCIPY = False


# ---------------------------------------------------------------- structures
def build(n, edges, S):
    M, B = split_edges(edges, S)
    badj = adj_masks(n, B)
    info = []
    for u, v in M:
        du, cu = sp_counts(n, badj, u)
        dv, cv = sp_counts(n, badj, v)
        l = du[v]
        sigma = cu[v]
        onv = [cu[x] * cv[x] if (du[x] >= 0 and dv[x] >= 0 and du[x] + dv[x] == l)
               else 0 for x in range(n)]
        info.append({"u": u, "v": v, "l": l, "sigma": sigma, "onv": onv,
                     "du": du, "dv": dv})
    return M, B, badj, info


def enum_shortest_paths(n, badj, inf, cap=20000):
    """All shortest u-v paths (vertex tuples).  None if > cap."""
    u, v, l, du, dv = inf["u"], inf["v"], inf["l"], inf["du"], inf["dv"]
    paths, stack = [], [(u, (u,))]
    while stack:
        x, p = stack.pop()
        if x == v:
            paths.append(p)
            if len(paths) > cap:
                return None
            continue
        m = badj[x]
        while m:
            y = (m & -m).bit_length() - 1
            m &= m - 1
            if du[y] == du[x] + 1 and du[y] + dv[y] == l:
                stack.append((y, p + (y,)))
    return paths


# ------------------------------------------------------------- candidate C3
def test_C3(n, edges, S):
    """Returns (verdict, detail). verdicts:
       PASS_UNIFORM / PASS_LP(exact) / KILL_HUB(exact) / KILL_LP(exact) /
       PASS_LP_FLOAT / UNRESOLVED"""
    M, B, badj, info = build(n, edges, S)
    # (a) uniform routing, exact
    g = [Fraction(0)] * n
    for inf in info:
        w = inf["l"] + 1
        for x in range(n):
            if inf["onv"][x]:
                g[x] += Fraction(w * inf["onv"][x], inf["sigma"])
    if max(g) <= n:
        return "PASS_UNIFORM", None
    # (b) hub kill, exact integers
    for x in range(n):
        L = sum(inf["l"] + 1 for inf in info if inf["onv"][x] == inf["sigma"])
        if L > n:
            return "KILL_HUB", ("hub", x, L)
    if not HAVE_SCIPY:
        return "UNRESOLVED", "no scipy"
    # (c) LP min-max-load over shortest-path routings
    allpaths = []
    for k, inf in enumerate(info):
        ps = enum_shortest_paths(n, badj, inf)
        if ps is None:
            return "UNRESOLVED", "path blowup"
        allpaths.append(ps)
    nv = sum(len(p) for p in allpaths) + 1   # lambdas + z
    zi = nv - 1
    Aub, bub = [], []
    for x in range(n):
        row = [0.0] * nv
        col = 0
        for k, ps in enumerate(allpaths):
            w = info[k]["l"] + 1
            for p in ps:
                if x in p:
                    row[col] = w
                col += 1
        row[zi] = -1.0
        Aub.append(row); bub.append(0.0)
    Aeq, beq = [], []
    col = 0
    for k, ps in enumerate(allpaths):
        row = [0.0] * nv
        for _ in ps:
            row[col] = 1.0
            col += 1
        Aeq.append(row); beq.append(1.0)
    c = [0.0] * nv; c[zi] = 1.0
    res = linprog(c, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq,
                  bounds=[(0, None)] * nv, method="highs")
    if not res.success:
        return "UNRESOLVED", "LP fail"
    if res.fun <= n + 1e-9:
        # exact re-verification of feasibility at load <= n
        lam = [Fraction(max(x, 0.0)).limit_denominator(10**7) for x in res.x[:zi]]
        col = 0
        ok = True
        gg = [Fraction(0)] * n
        for k, ps in enumerate(allpaths):
            tot = sum(lam[col + i] for i in range(len(ps)))
            if tot == 0:
                ok = False; break
            w = info[k]["l"] + 1
            for i, p in enumerate(ps):
                lp = lam[col + i] / tot
                for x in set(p):
                    gg[x] += w * lp
            col += len(ps)
        if ok and max(gg) <= n:
            return "PASS_LP", None
        return "PASS_LP_FLOAT", float(res.fun)   # float says feasible; exact repair failed
    # LP says min-max load > n: exact kill via rationalized dual on vertices
    # dual: y >= 0 on vertices, sum y = 1, bound = sum_uv (l+1) min_{P} y(P)
    y_raw = None
    try:
        y_raw = [-m for m in res.ineqlin.marginals]  # duals of load rows
    except Exception:
        pass
    if y_raw is not None:
        for den in (10**4, 10**6, 10**9):
            y = [Fraction(max(t, 0.0)).limit_denominator(den) for t in y_raw]
            tot = sum(y)
            if tot == 0:
                continue
            y = [t / tot for t in y]
            bound = Fraction(0)
            for k, ps in enumerate(allpaths):
                w = info[k]["l"] + 1
                bound += w * min(sum(y[x] for x in set(p)) for p in ps)
            if bound > n:
                return "KILL_LP", ("dual", [str(t) for t in y], str(bound))
    return "UNRESOLVED", ("lp_val", float(res.fun))


# ------------------------------------------------------------- candidate C2
def test_C2(n, edges, S):
    """Returns (verdict, detail): PASS_UNIFORM(exact) / PASS_LP_FLOAT /
       KILL_FARKAS(exact) / UNRESOLVED"""
    M, B, badj, info = build(n, edges, S)
    # (a) uniform shortest-path flow, exact edge loads
    load = {}
    for inf in info:
        u, v, l, du, dv, sig = inf["u"], inf["v"], inf["l"], inf["du"], inf["dv"], inf["sigma"]
        cu = sp_counts(n, badj, u)[1]
        cv = sp_counts(n, badj, v)[1]
        for (a, b) in B:
            f = Fraction(0)
            for (x, y) in ((a, b), (b, a)):
                if du[x] >= 0 and dv[y] >= 0 and du[x] + 1 + dv[y] == l:
                    f += Fraction(cu[x] * cv[y], sig)
            if f:
                load[(a, b)] = load.get((a, b), Fraction(0)) + f
    if all(f <= 1 for f in load.values()):
        return "PASS_UNIFORM", None
    if not HAVE_SCIPY:
        return "UNRESOLVED", "no scipy"
    # (b) LP feasibility: per-commodity edge flows, congestion <= 1 + slack
    K, mB = len(M), len(B)
    arcs = [(a, b) for (a, b) in B] + [(b, a) for (a, b) in B]
    nv = K * 2 * mB + mB           # flows + per-edge slack
    def fvar(k, ai): return k * 2 * mB + ai
    def svar(e): return K * 2 * mB + e
    Aeq, beq = [], []
    for k, (u, v) in enumerate(M):
        for x in range(n):
            row = [0.0] * nv
            nz = False
            for ai, (p, q) in enumerate(arcs):
                if p == x: row[fvar(k, ai)] += 1.0; nz = True
                if q == x: row[fvar(k, ai)] -= 1.0; nz = True
            if nz:
                Aeq.append(row)
                beq.append(1.0 if x == u else (-1.0 if x == v else 0.0))
    Aub, bub = [], []
    for e in range(mB):
        row = [0.0] * nv
        for k in range(K):
            row[fvar(k, e)] = 1.0
            row[fvar(k, e + mB)] = 1.0
        row[svar(e)] = -1.0
        Aub.append(row); bub.append(1.0)
    c = [0.0] * nv
    for e in range(mB):
        c[svar(e)] = 1.0
    res = linprog(c, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq,
                  bounds=[(0, None)] * nv, method="highs")
    if not res.success:
        return "UNRESOLVED", "LP fail"
    if res.fun <= 1e-9:
        return "PASS_LP_FLOAT", None
    # infeasible at congestion 1: exact Farkas certificate
    try:
        y = list(res.eqlin.marginals)
        w = [-t for t in res.ineqlin.marginals]
    except Exception:
        return "UNRESOLVED", ("no duals", float(res.fun))
    for den in (10**4, 10**6, 10**9):
        yr = [Fraction(t).limit_denominator(den) for t in y]
        wr = [max(Fraction(t).limit_denominator(den), Fraction(0)) for t in w]
        # Farkas: need y^T A_eq + w^T A_ub >= 0 per flow var, w_e >= coefficient
        # structure: flow var (k,ai): y-part + w_e >= 0 ; slack var e: -w_e + 1*0...
        # verify directly on matrices (exact):
        okcols = True
        for k in range(K):
            for ai, (p, q) in enumerate(arcs):
                colv = Fraction(0)
                # eq rows for commodity k only touch its own vars
                idx = 0
                for kk, (u, v) in enumerate(M):
                    for x in range(n):
                        # row exists only if some arc touches x; recompute presence
                        pass
                okcols = False
                break
            break
        # matrix bookkeeping is fiddly; rebuild exactly instead:
        rows_eq = []
        for k, (u, v) in enumerate(M):
            for x in range(n):
                nz = any(p == x or q == x for (p, q) in arcs)
                if nz:
                    rows_eq.append((k, x, 1 if x == u else (-1 if x == v else 0)))
        if len(rows_eq) != len(yr):
            continue
        good = True
        for k in range(K):
            for ai, (p, q) in enumerate(arcs):
                s = Fraction(0)
                for ri, (kk, x, bx) in enumerate(rows_eq):
                    if kk == k and (p == x or q == x):
                        s += yr[ri] * (1 if p == x else -1)
                e = ai % mB
                s += wr[e]
                if s < 0:
                    good = False; break
            if not good:
                break
        if good:
            # slack columns: -w_e >= 0 must NOT be required (slack has cost 1 in
            # the homogeneous system we certify {A_eq f = b, A_ub' f <= 1}: slack
            # columns absent).  RHS: y^T b + w^T 1 < 0 required.
            rhs = sum(yr[ri] * bx for ri, (kk, x, bx) in enumerate(rows_eq)) \
                  + sum(wr[e] for e in range(mB))
            if rhs < 0:
                return "KILL_FARKAS", ("farkas", [str(t) for t in yr], [str(t) for t in wr])
        # sign convention flip attempt
        yr2 = [-t for t in yr]
        good = True
        for k in range(K):
            for ai, (p, q) in enumerate(arcs):
                s = Fraction(0)
                for ri, (kk, x, bx) in enumerate(rows_eq):
                    if kk == k and (p == x or q == x):
                        s += yr2[ri] * (1 if p == x else -1)
                s += wr[ai % mB]
                if s < 0:
                    good = False; break
            if not good:
                break
        if good:
            rhs = sum(yr2[ri] * bx for ri, (kk, x, bx) in enumerate(rows_eq)) \
                  + sum(wr[e] for e in range(mB))
            if rhs < 0:
                return "KILL_FARKAS", ("farkas-neg", None, None)
    return "UNRESOLVED", ("lp_infeas_val", float(res.fun))


# -------------------------------------------------------------------- driver
def injected_instances():
    out = []
    # C_5[3] (N=15) and C_5[4] (N=20): blow-up cut classes 0,2 on side 1
    for q in (3, 4):
        n, edges, cl = c5_blowup([q] * 5)
        S = 0
        for v in cl[0] + cl[2]:
            S |= 1 << v
        out.append((f"C_5[{q}]", n, edges, S))
    n7, e7 = cycle(7)
    n, edges, cl = blowup(7, e7, [2] * 7)
    S = 0
    for v in cl[0] + cl[2] + cl[4]:
        S |= 1 << v
    out.append(("C_7[2]", n, edges, S))
    return out


def main():
    root = os.path.dirname(os.path.abspath(__file__))
    stats3, stats2 = {}, {}
    kills3, kills2 = [], []
    unres = []
    run_c2_max_n = 9
    for fn in sorted(os.listdir(root)):
        if not fn.startswith("dump_n") or not fn.endswith(".txt"):
            continue
        nn = int(fn[6:-4])
        with open(os.path.join(root, fn)) as f:
            lines = [l.split() for l in f if l.strip()]
        for g6, Ss in lines:
            n, edges = parse_graph6(g6)
            S = int(Ss)
            inst = gamma_of_instance(n, edges, S)
            near = inst["Gamma"] >= (n - 1) * (n - 1)
            v3, d3 = test_C3(n, edges, S)
            stats3[(n, v3)] = stats3.get((n, v3), 0) + 1
            if v3.startswith("KILL"):
                kills3.append((n, g6, S, v3, d3, inst["Gamma"]))
            elif v3 == "UNRESOLVED":
                unres.append(("C3", n, g6, S, d3))
            if n <= run_c2_max_n or near:
                v2, d2 = test_C2(n, edges, S)
                stats2[(n, v2)] = stats2.get((n, v2), 0) + 1
                if v2.startswith("KILL"):
                    kills2.append((n, g6, S, v2, d2, inst["Gamma"]))
                elif v2 == "UNRESOLVED":
                    unres.append(("C2", n, g6, S, d2))
    for name, n, edges, S in injected_instances():
        inst = gamma_of_instance(n, edges, S)
        v3, d3 = test_C3(n, edges, S)
        print(f"INJECTED {name}: Gamma={inst['Gamma']} N2={n*n}  C3={v3} {d3 if d3 else ''}")
        if n <= 15:
            v2, d2 = test_C2(n, edges, S)
            print(f"INJECTED {name}: C2={v2}")
    print("\n--- C3 (local load <= N) stats by (n, verdict):")
    for k in sorted(stats3):
        print(f"  n={k[0]:2d} {k[1]:14s} {stats3[k]}")
    print("--- C2 (edge congestion <= 1) stats by (n, verdict):")
    for k in sorted(stats2):
        print(f"  n={k[0]:2d} {k[1]:14s} {stats2[k]}")
    print(f"\nC3 kills: {len(kills3)}")
    for k in kills3[:20]:
        print("  KILL3", k)
    print(f"C2 kills: {len(kills2)}")
    for k in kills2[:20]:
        print("  KILL2", k)
    print(f"unresolved: {len(unres)}")
    for u in unres[:20]:
        print("  UNRES", u)
    with open(os.path.join(root, "candidate_kills.txt"), "w") as f:
        for k in kills3:
            f.write("KILL3 " + repr(k) + "\n")
        for k in kills2:
            f.write("KILL2 " + repr(k) + "\n")
        for u in unres:
            f.write("UNRES " + repr(u) + "\n")


if __name__ == "__main__":
    main()
