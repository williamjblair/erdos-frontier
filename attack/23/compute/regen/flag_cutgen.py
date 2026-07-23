#!/usr/bin/env python3
"""
BCL local-cut CUT-GENERATION (GPT Q19 box-QP separation; Q22 pseudocode was degenerate so implemented
from Q19's scheme). Corrected deficit framework (g_r=A_r-t*S_r, non-root edges only; U-stat clean).
Per rooted type sigma: precompute the class-pair edge-density tensor E_ab(H) (a,b range over profile
classes = independent subsets of the roots) and S_sigma(H). For a binary cut p in {0,1}^classes,
   g_{sigma,p}(H) = sum_{a<=b: p_a==p_b} E_ab(H)  -  t*S_sigma(H).
SEPARATION at LP optimum x*: M_ab = E_ab@x*, Sx = S@x*; minimize over p the same-side sum
   min_p [ sum_{a<=b:p_a==p_b} M_ab ] - t*Sx   (= weighted profile-MaxCut of M; enumerate 2^classes).
If that min < eta* - tol, the cut is violated by x*; add it and re-solve. Iterate.
Contradiction LP (HIGHS exact): max eta s.t. sum x=1, band on e/C(n,2), eta<=g_r@x for all rules.
eta<0 => d_mono* < t in the medium band.
"""
import sys, time, itertools
import numpy as np
import cvxpy as cp
import flag_engine as fe
import flag_sdp as fs
import flag_localcut as fl


def profile_classes(k, Asig):
    cls = []
    for r in range(k + 1):
        for S in itertools.combinations(range(k), r):
            if all(not ((Asig[a] >> b) & 1) for a in S for b in S if a < b):
                cls.append(frozenset(S))
    return cls


def precompute_type(states, k, Asig):
    sigma = (k, Asig); classes = profile_classes(k, Asig); nc = len(classes)
    cidx = {c: i for i, c in enumerate(classes)}
    Es = []; Ss = []
    for (n, A) in states:
        adj = [[bool((A[u] >> v) & 1) for v in range(n)] for u in range(n)]
        nk = 1
        for i in range(k):
            nk *= (n - i)
        nmk = n - k; Cnmk2 = nmk * (nmk - 1) / 2.0
        E = np.zeros((nc, nc)); S = 0.0
        if nk == 0 or Cnmk2 <= 0:
            Es.append(E); Ss.append(0.0); continue
        for R in itertools.permutations(range(n), k):
            if not fs._induces_sigma_ordered(A, R, sigma):
                continue
            S += 1.0
            Rset = set(R); rest = [w for w in range(n) if w not in Rset]
            cl = {w: cidx[frozenset(i for i in range(k) if adj[w][R[i]])] for w in rest}
            for ui in range(len(rest)):
                u = rest[ui]; Au = adj[u]; cu = cl[u]
                for vi in range(ui + 1, len(rest)):
                    v = rest[vi]
                    if Au[v]:
                        cv = cl[v]; a, b = (cu, cv) if cu <= cv else (cv, cu)
                        E[a][b] += 1.0 / Cnmk2
        Es.append(E / nk); Ss.append(S / nk)
    return np.array(Es), np.array(Ss), classes


def _pc(args):
    states, k, Asig = args
    return precompute_type(states, k, Asig)


def precompute_all(states, type_specs, workers=60):
    """Precompute (E,S,classes) for many rooted types IN PARALLEL across processes (use the cores)."""
    import concurrent.futures as cf
    args = [(states, k, A) for (k, A) in type_specs]
    out = []
    with cf.ProcessPoolExecutor(max_workers=workers) as ex:
        for (k, A), (E, S, cls) in zip(type_specs, ex.map(_pc, args)):
            out.append((k, A, E, S, cls))
    return out


def cut_from_p(E, S, p, t):
    nc = E.shape[1]
    same = np.zeros(E.shape[0])
    for a in range(nc):
        for b in range(a, nc):
            if p[a] == p[b]:
                same += E[:, a, b]
    return same - t * S


def cut_from_q(E, S, q, t):
    """General (fractional q) deficit row: sum_{a<=b} (q_a q_b+(1-q_a)(1-q_b)) E[:,a,b] - t S. Vectorized."""
    q = np.asarray(q, float)
    qc = np.outer(q, q) + np.outer(1 - q, 1 - q)      # nc x nc, symmetric
    # E stored upper-triangular (a<=b); contract
    return np.tensordot(E, qc, axes=([1, 2], [0, 1])) - t * S


def separate(E, S, x, t, exhaustive_max=20, restarts=400):
    """Return (min_deficit, best_p) for the most-violated binary cut of this type at distribution x.
    Binary p minimizing same-side edge sum = weighted profile-MaxCut of M=E@x. Exhaustive for small
    #classes, greedy local-search MaxCut heuristic for large (e.g. the empty k=5 type has 2^5 classes)."""
    import random
    M = np.tensordot(x, E, axes=(0, 0)); Sx = float(x @ S); nc = M.shape[0]
    W = M + M.T                              # symmetric weights; W[a,a]=2*M[a,a]
    diag = np.array([M[a, a] for a in range(nc)])
    def same_sum(p):
        pa = np.array(p)
        # sum_{a<=b: p_a==p_b} M[a,b]
        s = 0.0
        for a in range(nc):
            for b in range(a, nc):
                if pa[a] == pa[b]:
                    s += M[a, b]
        return s
    if nc <= exhaustive_max:
        best = (1e18, None)
        for p in itertools.product((0, 1), repeat=nc):
            g = same_sum(p) - t * Sx
            if g < best[0]:
                best = (g, p)
        return best
    # heuristic: maximize cut (minimize same-side) via random-restart local search
    best = (1e18, None)
    for _ in range(restarts):
        p = [random.randint(0, 1) for _ in range(nc)]
        improved = True
        while improved:
            improved = False
            for a in range(nc):
                # delta in same-side sum from flipping a: edges (a,b) with b on a's CURRENT side become cut;
                # edges (a,b) with b on the other side become same. delta = (other-side W) - (same-side W) [excl a]
                same_w = sum(M[min(a, b), max(a, b)] for b in range(nc) if b != a and p[b] == p[a])
                othr_w = sum(M[min(a, b), max(a, b)] for b in range(nc) if b != a and p[b] != p[a])
                if othr_w < same_w:          # flipping reduces same-side
                    p[a] ^= 1; improved = True
        g = same_sum(p) - t * Sx
        if g < best[0]:
            best = (g, tuple(p))
    return best


def solve_lp(G, dedge, ns, band, Mrows=None):
    """max eta s.t. sum x=1, band, G@x>=eta (deficit cuts), Mrows@x>=0 (moment-PSD cuts), x>=0."""
    x = cp.Variable(ns, nonneg=True); eta = cp.Variable()
    cons = [cp.sum(x) == 1, dedge @ x >= band[0], dedge @ x <= band[1], G @ x >= eta]
    if Mrows is not None and len(Mrows):
        M = np.asarray(Mrows, dtype=float)
        M = M / np.maximum(np.abs(M).max(axis=1, keepdims=True), 1e-30)
        cons.append(M @ x >= 0)
    pr = cp.Problem(cp.Maximize(eta), cons)
    v = pr.solve(solver=cp.HIGHS)
    return v, np.array(x.value).ravel()


def moment_types(N, smax=None):
    """Standard uncolored flag moment blocks that fit at order N (type k + flag s, k+2s<=N).
    smax caps the flag free-size s (keeps order-N moment blocks the same dims as a smaller order;
    valid because any s with k+2s<=N gives a genuine moment-PSD constraint). Returns (label,sigma,flags)."""
    K0 = (0, [])                      # empty type -> global block
    K1 = (1, [0])                     # single vertex
    EDGE = (2, fe.adj_from_edges(2, [(0, 1)]))
    NON = (2, [0, 0])                 # two non-adjacent roots
    cap = (lambda s: s if smax is None else min(s, smax))
    specs = []
    s0 = cap(N // 2)
    specs.append(("K0", K0, fs.enumerate_flags(K0, s0)))
    s1 = cap((N - 1) // 2)
    specs.append(("K1", K1, fs.enumerate_flags(K1, 1 + s1)))
    s2 = cap((N - 2) // 2)
    specs.append(("EDGE", EDGE, fs.enumerate_flags(EDGE, 2 + s2)))
    specs.append(("NON", NON, fs.enumerate_flags(NON, 2 + s2)))
    return specs


def precompute_moments(N, states, specs):
    """Per type, list of t x t moment matrices P^sigma(H) (raw counts), normalized per state to densities."""
    out = []
    for (lab, sigma, flags) in specs:
        k = sigma[0]; s = (flags[0][0] - k) if flags else 0
        mats = fs.P_sigma(N, states, sigma, flags)
        # normalize each P(H) by (n)_k * C(n-k,s)^2-ish embedding count to a density in [0,1] scale
        norm = []
        for (n, _A) in states:
            nk = 1
            for i in range(k):
                nk *= (n - i)
            from math import comb
            denom = nk * (comb(n - k, s) ** 2) if (nk > 0 and n - k >= s) else 1.0
            norm.append(denom if denom > 0 else 1.0)
        P = np.stack([mats[i] / norm[i] for i in range(len(states))], axis=0)  # states x t x t
        out.append((lab, len(flags), P))
        print(f"    moment block {lab}: t={len(flags)} flags (s={s})", flush=True)
    return out


def separate_moment(P, x, tol=1e-9, maxvecs=2):
    """At x*, M = sum_H x_H P[H]. Return list of cut rows r_H = v^T P[H] v for the most-negative
    eigenpairs of M (valid ineq r@x>=0 since M^sigma(graphon-sampling) is PSD)."""
    M = np.tensordot(x, P, axes=(0, 0))
    M = 0.5 * (M + M.T)
    w, V = np.linalg.eigh(M)
    cap = len(w) if maxvecs is None else min(maxvecs, len(w))
    sel = [j for j in range(cap) if w[j] < -tol]
    if not sel:
        return [], (w[0] if len(w) else 0.0), []
    Vs = V[:, sel]                                   # (tt, m)
    PV = np.tensordot(P, Vs, axes=([2], [0]))        # (ns, tt, m)
    R = np.einsum("Hik,ik->Hk", PV, Vs)              # (ns, m) = v_k^T P(H) v_k
    rows = [R[:, k] for k in range(len(sel))]
    vecs = [Vs[:, k] for k in range(len(sel))]
    return rows, (w[0] if len(w) else 0.0), vecs


def run(N, t, kmax_gen=3, band=(0.2486, 0.3197), maxit=60, tol=1e-7):
    t0 = time.time()
    states = fe.enumerate_graphs(N, triangle_free=True); ns = len(states)
    dedge = fs.edge_density(states)
    # base rules: enumerated k<=2 deficit cuts
    base = fl.gen_rules(k_max=2, grid=(0.0, 0.5, 1.0))
    G = np.unique(np.round(np.stack([fl.g_vec(states, k, A, s, p, t) for (k, A, s, p) in base], axis=0), 12), axis=0)
    # generation types: all triangle-free rooted types on k=2..kmax_gen vertices (serial precompute)
    types = []
    for k in range(2, kmax_gen + 1):
        for (_, A) in fe.enumerate_graphs(k, triangle_free=True):
            E, S, cls = precompute_type(states, k, A)
            types.append((k, A, E, S, cls))
        print(f"  precomputed k={k} types [{time.time()-t0:.0f}s]", flush=True)
    print(f"N={N} t={t}: states={ns} base-rules={G.shape[0]} gen-types={len(types)} [{time.time()-t0:.0f}s]", flush=True)
    v, x = solve_lp(G, dedge, ns, band)
    print(f"  iter0: eta={v:+.6f} rules={G.shape[0]}", flush=True)
    for it in range(1, maxit + 1):
        added = 0
        newcuts = []
        for (k, A, E, S, cls) in types:
            g, p = separate(E, S, x, t)
            if g < v - tol:
                newcuts.append(cut_from_p(E, S, p, t)); added += 1
        if not newcuts:
            print(f"  iter{it}: no violated cut -> CONVERGED", flush=True); break
        G = np.vstack([G] + newcuts)
        v, x = solve_lp(G, dedge, ns, band)
        if it <= 5 or it % 5 == 0:
            print(f"  iter{it}: added {added} eta={v:+.6f} rules={G.shape[0]} [{time.time()-t0:.0f}s]", flush=True)
        if v < -tol:
            print(f"  iter{it}: eta={v:+.6f} < 0 -> medium band CLOSED at t={t}!", flush=True); break
    verdict = f"CLOSED (d_mono*<{t})" if v < -tol else f"NOT closed (eta={v:+.6f}>=0; bound > {t})"
    print(f"FINAL N={N} t={t}: eta*={v:+.6f} -> {verdict} [{time.time()-t0:.0f}s]", flush=True)
    return v


def run_full(N, t, kmax_gen=3, band=(0.2486, 0.3197), maxit=120, tol=1e-7, use_moments=True):
    """Deficit cut-generation PLUS rank-one moment-PSD cuts (LP outer-approx of flag positivity)."""
    t0 = time.time()
    states = fe.enumerate_graphs(N, triangle_free=True); ns = len(states)
    dedge = fs.edge_density(states)
    base = fl.gen_rules(k_max=2, grid=(0.0, 0.5, 1.0))
    G = np.unique(np.round(np.stack([fl.g_vec(states, k, A, s, p, t) for (k, A, s, p) in base], axis=0), 12), axis=0)
    types = []
    for k in range(2, kmax_gen + 1):
        for (_, A) in fe.enumerate_graphs(k, triangle_free=True):
            E, S, cls = precompute_type(states, k, A)
            types.append((k, A, E, S, cls))
        print(f"  precomputed deficit k={k} types [{time.time()-t0:.0f}s]", flush=True)
    moms = precompute_moments(N, states, moment_types(N)) if use_moments else []
    print(f"N={N} t={t}: states={ns} base={G.shape[0]} gen-types={len(types)} moment-blocks={len(moms)} [{time.time()-t0:.0f}s]", flush=True)
    Mrows = []
    v, x = solve_lp(G, dedge, ns, band, Mrows)
    print(f"  iter0: eta={v:+.7f} rules={G.shape[0]} mcuts=0", flush=True)
    for it in range(1, maxit + 1):
        added = 0; newcuts = []
        for (k, A, E, S, cls) in types:
            g, p = separate(E, S, x, t)
            if g < v - tol:
                newcuts.append(cut_from_p(E, S, p, t)); added += 1
        madded = 0; mn = 0.0
        if use_moments:
            for (lab, tdim, P) in moms:
                rows, lam, _ = separate_moment(P, x)
                mn = min(mn, lam)
                for r in rows:
                    Mrows.append(r); madded += 1
        if not newcuts and madded == 0:
            print(f"  iter{it}: no violated cut -> CONVERGED (min moment-eig={mn:+.2e})", flush=True); break
        if newcuts:
            G = np.vstack([G] + newcuts)
        v, x = solve_lp(G, dedge, ns, band, Mrows)
        if it <= 8 or it % 5 == 0:
            print(f"  iter{it}: +{added}def +{madded}mom eta={v:+.7f} rules={G.shape[0]} mcuts={len(Mrows)} mineig={mn:+.2e} [{time.time()-t0:.0f}s]", flush=True)
        if v < -tol:
            print(f"  iter{it}: eta={v:+.7f} < 0 -> medium band CLOSED at t={t}!", flush=True); break
    verdict = f"CLOSED (d_mono*<{t})" if v < -tol else f"NOT closed (eta={v:+.7f}>=0)"
    print(f"FINAL N={N} t={t}: eta*={v:+.7f} -> {verdict} [{time.time()-t0:.0f}s]", flush=True)
    return v


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "run"
    if mode == "full":
        N = int(sys.argv[2]) if len(sys.argv) > 2 else 8
        kg = int(sys.argv[3]) if len(sys.argv) > 3 else 3
        t = float(sys.argv[4]) if len(sys.argv) > 4 else 2.0/25
        run_full(N, t, kmax_gen=kg)
    else:
        N = int(sys.argv[1]) if len(sys.argv) > 1 else 8
        kg = int(sys.argv[2]) if len(sys.argv) > 2 else 3
        ts = [float(sys.argv[3])] if len(sys.argv) > 3 else (0.085, 2.0/25)
        for t in ts:
            run(N, t, kmax_gen=kg)
    print("DONE", flush=True)
