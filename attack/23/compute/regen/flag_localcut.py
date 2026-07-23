#!/usr/bin/env python3
"""
UNCOLORED BCL-style local-cut SDP (GPT Q19 route). Bound the max-cut deficit d_mono* = (e - MaxCut)/C(N,2)
over triangle-free graphs WITHOUT fixing a coloring: for every rooted CUT RULE (sigma, root-sides s, profile
probs p), an actual constructed bipartition gives  d_mono* <= C_{sigma,p}(graphon).  So
   max z  s.t.  sum x=1, x>=0, d_edge band, moment M^rho(x) >> 0, z <= <C_rule, x> for every rule.
z* upper-bounds d_mono*. BCL's published uncolored local-cut method reaches 2/23.5=0.0851 (vs our
single-displayed-cut switching stuck at ~0.10). Target: <= 2/25 = 0.08.

C_{sigma,p}(H) = avg over root-embeddings R (inducing sigma) of (1/C(n,2)) sum_{edges (u,v)}
   [ q_u q_v + (1-q_u)(1-q_v) ],   q_w = P[w on side 0] = s_i if w=R[i] else p_{alpha(w)},
   alpha(w) = { i : w ~ R[i] }.
"""
import sys, itertools, time
import numpy as np
import cvxpy as cp
import flag_engine as fe
import flag_sdp as fs


def cut_vec(states, k, Asig, sides, pmap):
    """Per-state C_{sigma,p}. sigma=(k,Asig) rooted type; sides=tuple len k in {0,1}; pmap: dict
    frozenset(subset of range(k)) -> p in [0,1] (side-0 prob for a non-root with that root-adjacency)."""
    sigma = (k, Asig)
    out = []
    for (n, A) in states:
        if n < 2:
            out.append(0.0); continue
        adj = [[bool((A[u] >> v) & 1) for v in range(n)] for u in range(n)]
        embeds = 0; acc = 0.0
        Cn2 = n * (n - 1) / 2.0
        for R in itertools.permutations(range(n), k):
            if not fs._induces_sigma_ordered(A, R, sigma):
                continue
            embeds += 1
            Rset = set(R); pos = {R[i]: i for i in range(k)}
            q = [0.0] * n
            for w in range(n):
                if w in Rset:
                    q[w] = float(sides[pos[w]])
                else:
                    alpha = frozenset(i for i in range(k) if adj[w][R[i]])
                    q[w] = pmap.get(alpha, 0.5)
            s = 0.0
            for u in range(n):
                Au = adj[u]
                for v in range(u + 1, n):
                    if Au[v]:
                        s += q[u] * q[v] + (1 - q[u]) * (1 - q[v])
            acc += s / Cn2
        out.append(acc / embeds if embeds else 0.0)
    return np.array(out)


def g_vec(states, k, Asig, sides, pmap, t=2.0/25):
    """GPT Q21 FIX: RAW deficit functional g_r(H) = A_r(H) - t*S_r(H), a graphon-linear U-statistic
    (NO conditional division by embedding count). g_r(H) = (1/(n)_k) * sum_{R induces sigma}
    [ (constructed-cut mono density over H) - t ].  Used in the contradiction LP:
    if d_mono*(W) >= t then every embedding's cut costs >= t so g_r(W) >= 0; eta*<0 => no counterexample."""
    sigma = (k, Asig)
    out = []
    for (n, A) in states:
        if n < 2:
            out.append(0.0); continue
        adj = [[bool((A[u] >> v) & 1) for v in range(n)] for u in range(n)]
        nk = 1
        for i in range(k):
            nk *= (n - i)                      # falling factorial (n)_k = #ordered k-tuples
        nmk = n - k
        Cnmk2 = nmk * (nmk - 1) / 2.0          # C(n-k,2): pairs among NON-root vertices (order k+2)
        if Cnmk2 <= 0:
            out.append(0.0); continue
        g = 0.0
        for R in itertools.permutations(range(n), k):
            if not fs._induces_sigma_ordered(A, R, sigma):
                continue
            Rset = set(R); pos = {R[i]: i for i in range(k)}
            rest = [w for w in range(n) if w not in Rset]
            q = {}
            for w in rest:
                alpha = frozenset(i for i in range(k) if adj[w][R[i]])
                q[w] = pmap.get(alpha, 0.5)
            cm = 0.0                            # mono edges among NON-root vertices only (graphon limit)
            for ui in range(len(rest)):
                u = rest[ui]; Au = adj[u]
                for vi in range(ui + 1, len(rest)):
                    v = rest[vi]
                    if Au[v]:
                        cm += q[u] * q[v] + (1 - q[u]) * (1 - q[v])
            g += (cm / Cnmk2 - t)
        out.append(g / nk if nk else 0.0)
    return np.array(out)


def gen_rules(k_max=3, grid=(0.0, 0.5, 1.0)):
    """Generate cut rules (k, Asig, sides, pmap) for k=0..k_max, all triangle-free rooted types,
    root-sides, and profile-prob assignments over `grid`. Profiles = independent subsets of roots."""
    rules = []
    for k in range(0, k_max + 1):
        # enumerate rooted types: triangle-free graphs on k labeled vertices
        if k == 0:
            types = [(0, [])]
        else:
            types = [(k, A) for (_, A) in fe.enumerate_graphs(k, triangle_free=True)]
            # use LABELED types: also include all labelings? enumerate_graphs gives iso classes;
            # for rooted types labeling matters but cut value is symmetric enough; keep iso reps.
        for (kk, Asig) in types:
            # realizable profiles: subsets S of range(k) that are independent in Asig (no two adjacent roots)
            profs = []
            for r in range(k + 1):
                for S in itertools.combinations(range(k), r):
                    ok = all(not ((Asig[a] >> b) & 1) for a in S for b in S if a < b)
                    if ok:
                        profs.append(frozenset(S))
            profs = list(dict.fromkeys(profs))
            for sides in itertools.product((0, 1), repeat=k):
                for pvals in itertools.product(grid, repeat=len(profs)):
                    pmap = {profs[i]: pvals[i] for i in range(len(profs))}
                    rules.append((k, Asig, sides, pmap))
    return rules


def solve(N, k_max=3, band=(0.2486, 0.3197), kmax_types=2):
    t0 = time.time()
    states = fe.enumerate_graphs(N, triangle_free=True)
    ns = len(states)
    dedge = fs.edge_density(states)
    print(f"=== uncolored local-cut SDP N={N} (band={band}) === states={ns} [{time.time()-t0:.0f}s]", flush=True)
    # moment types (uncolored): K1 (order up to N), edge/non-edge 2-root
    tf = []
    for k in range(1, kmax_types + 1):
        for (_, A) in fe.enumerate_graphs(k, triangle_free=True):
            sigma = (k, A)
            for s in range(1, (N - k) // 2 + 1):
                fl = fs.enumerate_flags(sigma, k + s)
                if len(fl) >= 2:
                    tf.append((sigma, fl))
    Pflats = []
    for (sigma, flags) in tf:
        mats = fs.P_sigma(N, states, sigma, flags); t = len(flags)
        Pflats.append((np.stack([m.ravel() for m in mats], axis=1), t))
    rules = gen_rules(k_max=k_max, grid=(0.0, 0.5, 1.0))
    Cmat0 = np.stack([cut_vec(states, k, Asig, sides, pmap) for (k, Asig, sides, pmap) in rules], axis=0)
    Cmat = np.unique(np.round(Cmat0, 9), axis=0)     # dedupe identical cut functionals
    print(f"  moment blocks={len(Pflats)} cut-rules={len(rules)}->dedup {Cmat.shape[0]} [{time.time()-t0:.0f}s]; solving ...", flush=True)

    x = cp.Variable(ns, nonneg=True); z = cp.Variable()
    cons = [cp.sum(x) == 1, dedge @ x >= band[0], dedge @ x <= band[1]]
    for (Pflat, t) in Pflats:
        M = cp.reshape(Pflat @ x, (t, t), order='C'); cons.append(0.5 * (M + M.T) >> 0)
    cons.append(Cmat @ x >= z)          # z <= <C_rule, x> for every rule
    prob = cp.Problem(cp.Maximize(z), cons)
    try:
        val = prob.solve(solver=cp.SDPA, maxIteration=300, epsilonStar=1e-8, epsilonDash=1e-8,
                         numThreads=64, isDimacs=True)
        print(f"  [SDPA] status={prob.status}", flush=True)
    except Exception as e:
        print(f"  [SDPA failed: {type(e).__name__}: {e}] falling back to SCS", flush=True)
        val = prob.solve(solver=cp.SCS, max_iters=200000, eps_abs=1e-7, eps_rel=1e-7)
    print(f"  max d_mono* (z) = {val:.6f}  (beta/N^2 <= {val/2:.5f})  status={prob.status} [{time.time()-t0:.0f}s]", flush=True)
    print(f"  (BCL published = 0.0851; our single-cut switching ~0.10; target = 0.08)", flush=True)
    return val


if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    kmax = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    solve(N, k_max=kmax)
    print("DONE", flush=True)
