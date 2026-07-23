#!/usr/bin/env python3
"""
GPT Q24 cut-deficit LOCALIZER (doubly-nonnegative lift of the BCL deficit).

For rooted type sigma=(k,Asig), profile classes alpha (independent subsets of roots),
cut probabilities p_alpha in [0,1], and t=2/25, define the nc x nc matrix per graph H:

  L_{a,b}^{sigma,p}(H) = 1/((n)_k (n-k)_4) *
        sum_{theta, z, z', u, v all distinct}
           1[H[theta]=sigma] 1[pi(z)=a] 1[pi(z')=b]
           ( 1[uv in E] q_{pi(u),pi(v)}  -  t )

with q_{a,b} = p_a p_b + (1-p_a)(1-p_b)   (same-side prob of the BCL cut).
theta = ordered k-tuple of roots inducing sigma; z,z',u,v = 4 distinct non-root vertices;
pi(w) = profile class of w (set of roots adjacent to w).

SOUNDNESS (for a triangle-free counterexample graphon W with d_mono(W) > t under max cut):
for every fixed theta the profile-cut is a COMPLETE cut of W, so its mono-density
>= d_mono(W) > t, hence delta_p(theta) := E_{u,v}[1[uv]q - t] >= d_mono - t > 0 POINTWISE.
Therefore  L = int_theta delta_p(theta) rho(theta) rho(theta)^T dtheta  is PSD and
completely-positive (so entrywise >= 0).  => valid cuts:  L(x) >> 0  and  L_{ab}(x) >= 0.

This module: exact per-state L via a closed form (validated against a slow direct
reference), plus the mandated audits (symmetry, vertex-deletion U-statistic, row-sums).
"""
import sys, itertools
import numpy as np
import flag_engine as fe
import flag_sdp as fs
import flag_cutgen as fc

T_DEFAULT = 2.0 / 25.0


def _norm_rows(Mrows):
    """Scale each >=0 cut row to max|.|=1 (constraint r@x>=0 is scale-invariant) for HIGHS stability."""
    M = np.asarray(Mrows, dtype=float)
    if M.ndim == 1:
        M = M[None, :]
    s = np.maximum(np.abs(M).max(axis=1, keepdims=True), 1e-30)
    return M / s


def qmat(p):
    p = np.asarray(p, float)
    return np.outer(p, p) + np.outer(1 - p, 1 - p)   # q[a,b] = p_a p_b + (1-p_a)(1-p_b)


def _classes_and_labels(n, A, sigma, classes):
    """Return (cidx) helper; per (theta) we compute labels on the fly."""
    return {c: i for i, c in enumerate(classes)}


def localizer_state_fast(n, A, sigma, classes, cidx, Q, t):
    """Closed-form nc x nc raw sum T(H) = sum_theta sum_{z,z',u,v distinct} ... (NOT yet /norm)."""
    k, Asig = sigma
    nc = len(classes)
    adj = [[bool((A[u] >> v) & 1) for v in range(n)] for u in range(n)]
    T = np.zeros((nc, nc))
    allv = range(n)
    for R in itertools.permutations(allv, k):
        if not fs._induces_sigma_ordered(A, R, sigma):
            continue
        W = [w for w in allv if w not in R]
        m = len(W)
        if m < 4:
            continue
        # class label of each non-root vertex
        lab = []
        for w in W:
            prof = frozenset(i for i in range(k) if adj[w][R[i]])
            lab.append(cidx[prof])
        lab = np.array(lab)
        # class counts A_a
        Acnt = np.bincount(lab, minlength=nc).astype(float)
        # h(u,v) = 1[uv in E] q_{c(u),c(v)} - t  for u!=v in W ; build m x m (zero diag)
        h = np.full((m, m), -t)
        for iu in range(m):
            u = W[iu]; Au = adj[u]; cu = lab[iu]
            for iv in range(m):
                if iv == iu:
                    continue
                v = W[iv]
                if Au[v]:
                    h[iu, iv] = Q[cu, lab[iv]] - t
                # else stays -t
        np.fill_diagonal(h, 0.0)
        # H0, H1_a = sum_{u!=v} h 1[c(u)=a], H2_{a,b}=sum_{u!=v} h 1[c(u)=a]1[c(v)=b]
        H0 = h.sum()
        # H2[a,b] = sum over u in class a, v in class b (u!=v) of h[u,v]
        H2 = np.zeros((nc, nc))
        for a in range(nc):
            ua = np.where(lab == a)[0]
            if len(ua) == 0:
                continue
            ha = h[ua, :]                      # rows = class-a u
            for b in range(nc):
                vb = np.where(lab == b)[0]
                if len(vb) == 0:
                    continue
                H2[a, b] = ha[:, vb].sum()
        H1 = H2.sum(axis=1)                    # H1[a] = sum_b H2[a,b]
        # T_{a,b} = Aa Ab H0 - 2 Aa H1[b] - 2 Ab H1[a] + 2 H2[a,b] + 1[a=b](4 H1[a] - Aa H0)
        Tt = (np.outer(Acnt, Acnt) * H0
              - 2 * np.outer(Acnt, H1)
              - 2 * np.outer(H1, Acnt)
              + 2 * H2)
        diagadd = 4 * H1 - Acnt * H0
        Tt[np.diag_indices(nc)] += diagadd
        T += Tt
    return T


def localizer_affine_state(n, A, sigma, classes, cidx, t):
    """One theta-pass: return (const nc x nc, grad nc x nc x nc x nc) s.t. for ANY symmetric Q,
       T(Q)[a,b] = const[a,b] + sum_{c,d} grad[a,b,c,d] Q[c,d].   (L = T / norm.)"""
    k, Asig = sigma
    nc = len(classes)
    adj = [[bool((A[u] >> v) & 1) for v in range(n)] for u in range(n)]
    const = np.zeros((nc, nc)); grad = np.zeros((nc, nc, nc, nc))
    I = np.eye(nc)
    for R in itertools.permutations(range(n), k):
        if not fs._induces_sigma_ordered(A, R, sigma):
            continue
        W = [w for w in range(n) if w not in R]
        if len(W) < 4:
            continue
        lab = np.array([cidx[frozenset(i for i in range(k) if adj[w][R[i]])] for w in W])
        Acnt = np.bincount(lab, minlength=nc).astype(float)
        # Eord[a,b] = # ordered (u,v) u!=v, c(u)=a, c(v)=b, uv in E
        Eord = np.zeros((nc, nc))
        for iu in range(len(W)):
            u = W[iu]; Au = adj[u]; a = lab[iu]
            for iv in range(len(W)):
                if iv != iu and Au[W[iv]]:
                    Eord[a, lab[iv]] += 1.0
        Pord = np.outer(Acnt, Acnt) - np.diag(Acnt)        # ordered pairs by class (u!=v)
        # ---- const (Q=0): H2_0 = -t Pord ----
        H2_0 = -t * Pord
        H0_0 = H2_0.sum(); H1_0 = H2_0.sum(axis=1)
        c_ab = (np.outer(Acnt, Acnt) * H0_0 - 2 * np.outer(Acnt, H1_0) - 2 * np.outer(H1_0, Acnt) + 2 * H2_0)
        c_ab[np.diag_indices(nc)] += 4 * H1_0 - Acnt * H0_0
        const += c_ab
        # ---- grad[a,b,c,d] = Eord[c,d]*(Aa Ab - 2Aa d_bc - 2Ab d_ac + d_ab(4 d_ac - Aa)) + 2 d_ac d_bd Eord[a,b]
        AA = np.outer(Acnt, Acnt)                                  # [a,b]
        coef = AA[:, :, None, None] * np.ones((1, 1, nc, nc))      # Aa Ab term (times Eord later)
        # -2 Aa d_bc : nonzero when c=b -> term[a,b,c=b,d] = -2 Aa ; build via broadcasting over d
        t1 = np.zeros((nc, nc, nc, nc))
        # d_bc means c index == b: for each a,b,d set [a,b,b,d] -= 2 Aa
        for b in range(nc):
            t1[:, b, b, :] += -2 * Acnt[:, None]
        t2 = np.zeros((nc, nc, nc, nc))
        for a in range(nc):
            t2[a, :, a, :] += -2 * Acnt[:, None]      # -2 A_b d_ac : [a,b,c=a,d] = -2 A_b
        t3 = np.zeros((nc, nc, nc, nc))   # d_ab(4 d_ac - Aa)
        for a in range(nc):
            t3[a, a, a, :] += 4.0
            t3[a, a, :, :] += -Acnt[a]
        bracket = coef + t1 + t2 + t3
        grad += bracket * Eord[None, None, :, :]
        # + 2 d_ac d_bd Eord[a,b] : [a,b,a,b] += 2 Eord[a,b]
        for a in range(nc):
            for b in range(nc):
                grad[a, b, a, b] += 2.0 * Eord[a, b]
    return const, grad


def precompute_localizer_affine(states, sigma, t=T_DEFAULT, classes=None, support=None):
    k, Asig = sigma
    if classes is None:
        classes = fc.profile_classes(k, Asig)
    cidx = {c: i for i, c in enumerate(classes)}
    nc = len(classes)
    if support is None:
        support = sigma_support(states, sigma)
    CONST = {}; GRAD = {}
    for hi in support:
        n, A = states[hi]; nf = norm_factor(n, k)
        c, g = localizer_affine_state(n, A, sigma, classes, cidx, t)
        CONST[hi] = c / nf; GRAD[hi] = g / nf
    return CONST, GRAD, classes, support


def Lp_from_affine(CONST_agg, GRAD_agg, p):
    Q = qmat(p)
    return CONST_agg + np.einsum("abcd,cd->ab", GRAD_agg, Q)


def _agg_CG(CONST, GRAD, support, x):
    nc = next(iter(CONST.values())).shape[0]
    xs = np.array([x[hi] for hi in support])
    nz = np.nonzero(xs)[0]
    CA = np.zeros((nc, nc)); GA = np.zeros((nc, nc, nc, nc))
    suplist = list(support)
    for i in nz:
        hi = suplist[i]; CA += xs[i] * CONST[hi]; GA += xs[i] * GRAD[hi]
    return CA, GA


def separate_localizer_p(CONST, GRAD, support, x, restarts=12, iters=30, seed=0, tol=1e-9, grid=(0.0, 0.5, 1.0)):
    """Find p in [0,1]^nc minimizing lambda_min(L^{sigma,p}(x)). Return (p, lam, eigvec) or None.
    Fast: GA reshaped to (nc^2,nc^2) so L(p)=CA + (GA2 @ qflat(p)).reshape; coordinate descent on p."""
    nc = next(iter(CONST.values())).shape[0]
    CA, GA = _agg_CG(CONST, GRAD, support, x)
    GA2 = GA.reshape(nc * nc, nc * nc)
    def Lof(p):
        q = (np.outer(p, p) + np.outer(1 - p, 1 - p)).reshape(-1)
        L = CA + (GA2 @ q).reshape(nc, nc)
        return 0.5 * (L + L.T)
    rng = np.random.default_rng(seed)
    grid = np.asarray(grid)
    best = (1e18, None, None)
    for r in range(restarts):
        p = rng.random(nc) if r else np.full(nc, 0.5)
        for _ in range(iters):
            improved = False
            for a in range(nc):
                cur = p[a]; bestv = (cur, np.linalg.eigvalsh(Lof(p))[0])
                for cand in grid:
                    if cand == cur:
                        continue
                    p[a] = cand
                    lam = np.linalg.eigvalsh(Lof(p))[0]
                    if lam < bestv[1] - 1e-15:
                        bestv = (cand, lam)
                p[a] = bestv[0]
                if abs(p[a] - cur) > 1e-12:
                    improved = True
            if not improved:
                break
        w, V = np.linalg.eigh(Lof(p))
        if w[0] < best[0]:
            best = (w[0], p.copy(), V[:, 0])
    if best[0] < -tol:
        return best[1], best[0], best[2]
    return None


def localizer_state_slow(n, A, sigma, classes, cidx, Q, t):
    """Direct O(m^4) reference: sum over ordered distinct (z,z',u,v)."""
    k, Asig = sigma
    nc = len(classes)
    adj = [[bool((A[u] >> v) & 1) for v in range(n)] for u in range(n)]
    T = np.zeros((nc, nc))
    allv = list(range(n))
    for R in itertools.permutations(allv, k):
        if not fs._induces_sigma_ordered(A, R, sigma):
            continue
        Rset = set(R)
        W = [w for w in allv if w not in Rset]
        lab = {}
        for w in W:
            prof = frozenset(i for i in range(k) if adj[w][R[i]])
            lab[w] = cidx[prof]
        for (z, zp, u, v) in itertools.permutations(W, 4):
            h = (Q[lab[u], lab[v]] - t) if adj[u][v] else (-t)
            T[lab[z], lab[zp]] += h
    return T


def norm_factor(n, k):
    nk = 1
    for i in range(k):
        nk *= (n - i)
    m = n - k
    f4 = m * (m - 1) * (m - 2) * (m - 3) if m >= 4 else 0
    return nk * f4


def localizer_vec(states, sigma, p, t=T_DEFAULT, classes=None, fast=True):
    """Return (ns, nc, nc) array of L(H) = T(H)/norm(n,k)."""
    k, Asig = sigma
    if classes is None:
        classes = fc.profile_classes(k, Asig)
    cidx = {c: i for i, c in enumerate(classes)}
    Q = qmat(p)
    out = []
    fn = localizer_state_fast if fast else localizer_state_slow
    for (n, A) in states:
        nf = norm_factor(n, k)
        if nf == 0:
            out.append(np.zeros((len(classes), len(classes)))); continue
        out.append(fn(n, A, sigma, classes, cidx, Q, t) / nf)
    return np.array(out), classes


# ---------------- audits ----------------
def audit_fast_vs_slow(sigma, t=T_DEFAULT, seed=0, ntest=6):
    k, Asig = sigma
    classes = fc.profile_classes(k, Asig); cidx = {c: i for i, c in enumerate(classes)}
    rng = np.random.default_rng(seed)
    p = rng.random(len(classes)); Q = qmat(p)
    N = k + 4
    states = fe.enumerate_graphs(N, triangle_free=True)
    # restrict to states that actually contain sigma
    chosen = []
    for (n, A) in states:
        ok = any(fs._induces_sigma_ordered(A, R, sigma) for R in itertools.permutations(range(n), k))
        if ok:
            chosen.append((n, A))
        if len(chosen) >= ntest:
            break
    maxerr = 0.0
    for (n, A) in chosen:
        Tf = localizer_state_fast(n, A, sigma, classes, cidx, Q, t)
        Ts = localizer_state_slow(n, A, sigma, classes, cidx, Q, t)
        maxerr = max(maxerr, np.abs(Tf - Ts).max())
    return maxerr, len(chosen)


def audit_symmetry(states, sigma, p, t=T_DEFAULT):
    L, classes = localizer_vec(states, sigma, p, t)
    return np.abs(L - np.transpose(L, (0, 2, 1))).max()


def audit_rowsum_scalar(states, sigma, p, t=T_DEFAULT):
    """sum_{a,b} L_{ab}(H) should equal the scalar deficit g_{sigma,p}(H) (U-stat consistency)."""
    L, classes = localizer_vec(states, sigma, p, t)
    k, Asig = sigma
    # scalar deficit via flag_localcut g_vec with the SAME p mapping (profile-class -> p_alpha)
    pmap = {classes[i]: float(p[i]) for i in range(len(classes))}
    import flag_localcut as fl
    g = fl.g_vec(states, k, Asig, sides=None, pmap=pmap, t=t)
    Lsum = L.sum(axis=(1, 2))
    return np.abs(Lsum - g), g, Lsum


def audit_vertex_deletion(sigma, p, t=T_DEFAULT, nsample=4, seed=1):
    """L^{N+1}(H) == (1/(N+1)) sum_v L^N(H - v) for a few random order-(N+1) graphs."""
    k, Asig = sigma
    classes = fc.profile_classes(k, Asig); cidx = {c: i for i, c in enumerate(classes)}
    Q = qmat(p)
    N = k + 4
    big = fe.enumerate_graphs(N + 1, triangle_free=True)
    rng = np.random.default_rng(seed)
    idx = rng.choice(len(big), size=min(nsample, len(big)), replace=False)
    worst = 0.0
    for i in idx:
        n, A = big[i]
        Lbig = localizer_state_fast(n, A, sigma, classes, cidx, Q, t) / norm_factor(n, k)
        acc = np.zeros_like(Lbig)
        for v in range(n):
            verts = [w for w in range(n) if w != v]
            _, B = fe.induced(A, verts)
            acc += localizer_state_fast(n - 1, B, sigma, classes, cidx, Q, t) / norm_factor(n - 1, k)
        acc /= n
        worst = max(worst, np.abs(Lbig - acc).max())
    return worst


def cylinder_rows(states, sigma, p, t=T_DEFAULT, classes=None, support=None):
    """GPT Q26-C: edge/non-edge-split two-spectator cylinder localizers.
      C^eps_{a,b}(H) = 1/((N)_k (N-k)_4) sum_{theta,z,z',u,v distinct} 1[H[theta]=sigma]
          1[pi(z)=a] 1[pi(z')=b] 1[zz' in E <=> eps] (1[uv in E] q_{pi(u),pi(v)} - t)  >= 0.
    Each (eps,a,b) is a scalar LP row, valid for any counterexample (rooted deficit pointwise >=0).
    L_{ab} = C^0_{ab} + C^1_{ab}; imposing each >=0 is strictly stronger than L>>0.
    Returns dict {(eps,a,b): np.array(ns)}.  (N=9,k=5 -> nonroot set has 4 verts; brute 4-perms.)"""
    import itertools
    k, Asig = sigma
    if classes is None:
        classes = fc.profile_classes(k, Asig)
    cidx = {c: i for i, c in enumerate(classes)}
    nc = len(classes)
    Q = qmat(p)
    if support is None:
        support = sigma_support(states, sigma)
    ns = len(states)
    out = {(e, a, b): np.zeros(ns) for e in (0, 1) for a in range(nc) for b in range(nc)}
    for hi in support:
        n, A = states[hi]
        nf = norm_factor(n, k)
        if nf == 0:
            continue
        adj = [[bool((A[u] >> v) & 1) for v in range(n)] for u in range(n)]
        acc = {(e, a, b): 0.0 for e in (0, 1) for a in range(nc) for b in range(nc)}
        for R in itertools.permutations(range(n), k):
            if not fs._induces_sigma_ordered(A, R, sigma):
                continue
            W = [w for w in range(n) if w not in R]
            if len(W) < 4:
                continue
            lab = {w: cidx[frozenset(i for i in range(k) if adj[w][R[i]])] for w in W}
            for (z, zp, u, v) in itertools.permutations(W, 4):
                e = 1 if adj[z][zp] else 0
                h = (Q[lab[u], lab[v]] - t) if adj[u][v] else (-t)
                acc[(e, lab[z], lab[zp])] += h
        for key in acc:
            out[key][hi] = acc[key] / nf
    return out, classes


def localizer_vec_support(states, sigma, p, t=T_DEFAULT, classes=None, support=None):
    """Like localizer_vec but only computes L on `support` state-indices (others = 0)."""
    k, Asig = sigma
    if classes is None:
        classes = fc.profile_classes(k, Asig)
    cidx = {c: i for i, c in enumerate(classes)}
    Q = qmat(p); nc = len(classes)
    out = np.zeros((len(states), nc, nc))
    if support is None:
        support = range(len(states))
    for hi in support:
        n, A = states[hi]
        nf = norm_factor(n, k)
        if nf == 0:
            continue
        out[hi] = localizer_state_fast(n, A, sigma, classes, cidx, Q, t) / nf
    return out, classes


def sigma_support(states, sigma):
    k, Asig = sigma
    sup = []
    for hi, (n, A) in enumerate(states):
        if any(fs._induces_sigma_ordered(A, R, sigma) for R in itertools.permutations(range(n), k)):
            sup.append(hi)
    return sup


# C5 BCL-extremal cut (and its 5 rotations) on classes
#   [[], [0],[1],[2],[3],[4],[0,2],[0,3],[1,3],[1,4],[2,4]]
def c5_extremal_ps(classes):
    """For each rotation r of the max-cut 2-coloring of C5, the profile->side p vector."""
    cyc = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]
    out = []
    for shift in range(5):
        # max-cut: side0 = {shift, shift+2}, rest side1 ; blob i adj roots i-1,i+1 -> profile {i-1,i+1}
        side0 = {shift % 5, (shift + 2) % 5}
        p = []
        for c in classes:
            cl = sorted(c)
            if len(cl) == 2:
                # this is profile {i-1,i+1}; recover blob i = the vertex between them on C5
                a, b = cl
                # blob i s.t. {i-1,i+1}={a,b}: i = the common C5-neighbor of a and b
                nb = lambda x: {(x - 1) % 5, (x + 1) % 5}
                inter = nb(a) & nb(b)
                i = inter.pop() if inter else None
                p.append(1.0 if (i in side0) else 0.0)
            else:
                p.append(0.5)
        out.append(np.array(p))
    return out


def run_localized(N=9, t=T_DEFAULT, kmax_gen=4, band=(0.2486, 0.3197), maxit=200, tol=1e-7):
    import time
    import cvxpy as cp
    t0 = time.time()
    states = fe.enumerate_graphs(N, triangle_free=True); ns = len(states)
    dedge = fs.edge_density(states)
    base = fc.fl.gen_rules(k_max=2, grid=(0.0, 0.5, 1.0))
    G = np.unique(np.round(np.stack([fc.fl.g_vec(states, k, A, s, p, t) for (k, A, s, p) in base], axis=0), 12), axis=0)
    types = []
    for k in range(2, kmax_gen + 1):
        for (_, A) in fe.enumerate_graphs(k, triangle_free=True):
            E, S, cls = fc.precompute_type(states, k, A); types.append((k, A, E, S, cls))
    C5 = (5, fe.adj_from_edges(5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]))
    E5, S5, cls5 = fc.precompute_type(states, *C5); types.append((C5[0], C5[1], E5, S5, cls5))
    print(f"  deficit types ready ({len(types)}) [{time.time()-t0:.0f}s]", flush=True)
    moms = fc.precompute_moments(N, states, fc.moment_types(N))
    print(f"  moment blocks ready ({len(moms)}) [{time.time()-t0:.0f}s]", flush=True)
    classes5 = fc.profile_classes(*C5)
    sup5 = sigma_support(states, C5)
    print(f"  C5 support: {len(sup5)} states; nc={len(classes5)} [{time.time()-t0:.0f}s]", flush=True)
    # localizer p-pool, cached L-tensors
    pool = {}
    def add_p(p):
        key = tuple(np.round(p, 6))
        if key in pool:
            return
        Lt, _ = localizer_vec_support(states, C5, p, t, classes5, sup5)
        pool[key] = Lt
    for p in c5_extremal_ps(classes5):
        add_p(p)
    print(f"  localizer pool seeded: {len(pool)} cuts [{time.time()-t0:.0f}s]", flush=True)
    Mrows = []   # all >=0 rows (moment + localizer)

    def solve():
        x = cp.Variable(ns, nonneg=True); eta = cp.Variable()
        cons = [cp.sum(x) == 1, dedge @ x >= band[0], dedge @ x <= band[1], G @ x >= eta]
        if Mrows:
            cons.append(_norm_rows(Mrows) @ x >= 0)
        pr = cp.Problem(cp.Maximize(eta), cons)
        val = pr.solve(solver=cp.HIGHS)
        return val, np.array(x.value).ravel()

    v, x = solve()
    print(f"  iter0: eta={v:+.7f} def={G.shape[0]} mom+loc=0", flush=True)
    for it in range(1, maxit + 1):
        added = 0; newcuts = []
        for (k, A, E, S, cls) in types:
            g, p = fc.separate(E, S, x, t)
            if g < v - tol:
                newcuts.append(fc.cut_from_p(E, S, p, t)); added += 1
                if k == 5:                       # binding C5 deficit cut -> seed its localizer p
                    pp = np.array([float(p[i]) for i in range(len(cls))])
                    # map cls (C5 profile classes from precompute_type) to classes5 order
                    idx = [classes5.index(c) for c in cls]
                    pv = np.full(len(classes5), 0.5)
                    for j, ii in enumerate(idx):
                        pv[ii] = pp[j]
                    add_p(pv)
        madded = 0; mn = 0.0
        for (lab, tdim, P) in moms:
            rows, lam, _ = fc.separate_moment(P, x); mn = min(mn, lam)
            for r in rows:
                Mrows.append(r); madded += 1
        ladded = 0; lmn = 0.0
        for key, Lt in pool.items():
            Lx = np.tensordot(x, Lt, axes=(0, 0)); Lx = 0.5 * (Lx + Lx.T)
            w, V = np.linalg.eigh(Lx)
            lmn = min(lmn, w[0])
            for j in range(min(2, len(w))):
                if w[j] < -tol:
                    vv = V[:, j]
                    r = np.einsum("i,Hij,j->H", vv, Lt, vv)
                    Mrows.append(r); ladded += 1
            # entrywise
            neg = np.argwhere(Lx < -tol)
            for (a, b) in neg[:4]:
                Mrows.append(Lt[:, a, b]); ladded += 1
        if added == 0 and madded == 0 and ladded == 0:
            print(f"  iter{it}: CONVERGED (mom-eig={mn:+.2e} loc-eig={lmn:+.2e})", flush=True); break
        if newcuts:
            G = np.vstack([G] + newcuts)
        v, x = solve()
        if it <= 8 or it % 5 == 0:
            print(f"  iter{it}: +{added}d +{madded}m +{ladded}L eta={v:+.7f} def={G.shape[0]} ge0={len(Mrows)} meig={mn:+.1e} Leig={lmn:+.1e} pool={len(pool)} [{time.time()-t0:.0f}s]", flush=True)
        if v < -tol:
            print(f"  iter{it}: eta={v:+.7f} < 0 -> medium band CLOSED at t={t}!", flush=True); break
    verdict = "CLOSED" if v < -tol else "NOT closed"
    print(f"FINAL N={N} t={t}: eta*={v:+.7f} -> {verdict} [{time.time()-t0:.0f}s]", flush=True)
    return v


def run_localized_psep(N=9, t=T_DEFAULT, kmax_gen=4, band=(0.2486, 0.3197), maxit=200,
                       tol=1e-7, mom_maxvecs=6, loc_types=("C5",)):
    """Deficit + moment(rank-one, mom_maxvecs negs/iter) + localizer with most-violated-p separation."""
    import time, cvxpy as cp
    t0 = time.time()
    states = fe.enumerate_graphs(N, triangle_free=True); ns = len(states)
    dedge = fs.edge_density(states)
    base = fc.fl.gen_rules(k_max=2, grid=(0.0, 0.5, 1.0))
    G = np.unique(np.round(np.stack([fc.fl.g_vec(states, k, A, s, p, t) for (k, A, s, p) in base], axis=0), 12), axis=0)
    types = []
    for k in range(2, kmax_gen + 1):
        for (_, A) in fe.enumerate_graphs(k, triangle_free=True):
            E, S, cls = fc.precompute_type(states, k, A); types.append((k, A, E, S, cls))
    SIGS = {"C5": (5, fe.adj_from_edges(5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)])),
            "C4": (4, fe.adj_from_edges(4, [(0, 1), (1, 2), (2, 3), (3, 0)])),
            "K13": (4, fe.adj_from_edges(4, [(0, 1), (0, 2), (0, 3)])),
            "P4": (4, fe.adj_from_edges(4, [(0, 1), (1, 2), (2, 3)]))}
    for nm in loc_types:
        sig = SIGS[nm]; E, S, cls = fc.precompute_type(states, *sig); types.append((sig[0], sig[1], E, S, cls))
    print(f"  deficit types ready ({len(types)}) [{time.time()-t0:.0f}s]", flush=True)
    moms = fc.precompute_moments(N, states, fc.moment_types(N))
    print(f"  moment blocks ready [{time.time()-t0:.0f}s]", flush=True)
    locs = []   # (name, sigma, CONST, GRAD, support)
    for nm in loc_types:
        sig = SIGS[nm]
        CONST, GRAD, classes, sup = precompute_localizer_affine(states, sig, t)
        locs.append((nm, sig, CONST, GRAD, sup))
        print(f"  localizer affine [{nm}] ready: |sup|={len(sup)} nc={len(classes)} [{time.time()-t0:.0f}s]", flush=True)
    Mrows = []

    def solve():
        x = cp.Variable(ns, nonneg=True); eta = cp.Variable()
        cons = [cp.sum(x) == 1, dedge @ x >= band[0], dedge @ x <= band[1], G @ x >= eta]
        if Mrows:
            cons.append(_norm_rows(Mrows) @ x >= 0)
        pr = cp.Problem(cp.Maximize(eta), cons)
        val = pr.solve(solver=cp.HIGHS)
        return val, np.array(x.value).ravel()

    v, x = solve()
    print(f"  iter0: eta={v:+.7f}", flush=True)
    for it in range(1, maxit + 1):
        added = 0; newcuts = []
        for (k, A, E, S, cls) in types:
            g, p = fc.separate(E, S, x, t)
            if g < v - tol:
                newcuts.append(fc.cut_from_p(E, S, p, t)); added += 1
        madded = 0; mn = 0.0
        for (lab, tdim, P) in moms:
            rows, lam, _ = fc.separate_moment(P, x, maxvecs=mom_maxvecs); mn = min(mn, lam)
            for r in rows:
                Mrows.append(r); madded += 1
        ladded = 0; lmn = 0.0
        for (nm, sig, CONST, GRAD, sup) in locs:
            res = separate_localizer_p(CONST, GRAD, sup, x)
            if res is not None:
                p, lam, w = res; lmn = min(lmn, lam)
                # PSD min-eig cut row: r_H = w^T L^{sig,p}(H) w
                Q = qmat(p)
                r = np.zeros(ns)
                for hi in sup:
                    r[hi] = float(w @ (CONST[hi] + np.einsum("abcd,cd->ab", GRAD[hi], Q)) @ w)
                Mrows.append(r); ladded += 1
        if added == 0 and madded == 0 and ladded == 0:
            print(f"  iter{it}: CONVERGED (mom-eig={mn:+.2e} loc-eig={lmn:+.2e}) [{time.time()-t0:.0f}s]", flush=True); break
        if newcuts:
            G = np.vstack([G] + newcuts)
        v, x = solve()
        if it <= 10 or it % 5 == 0:
            print(f"  iter{it}: +{added}d +{madded}m +{ladded}L eta={v:+.7f} def={G.shape[0]} ge0={len(Mrows)} meig={mn:+.1e} Leig={lmn:+.1e} [{time.time()-t0:.0f}s]", flush=True)
        if v < -tol:
            print(f"  iter{it}: eta={v:+.7f} < 0 -> medium band CLOSED at t={t}!", flush=True); break
    verdict = "CLOSED" if v < -tol else "NOT closed"
    print(f"FINAL N={N} t={t}: eta*={v:+.7f} -> {verdict} [{time.time()-t0:.0f}s]", flush=True)
    return v


def run_hybrid(N=9, t=T_DEFAULT, kmax_gen=4, band=(0.2486, 0.3197), maxit=60, tol=1e-7,
               loc_types=("C5",), solver=None):
    """Conic moment-PSD (exact) + deficit + localizer-psep LP cuts. Estimates the TRUE order-N
    joint value (sign of eta) faster than the rank-one moment tail. (cross-check, not the exact cert)."""
    import time, cvxpy as cp
    t0 = time.time()
    states = fe.enumerate_graphs(N, triangle_free=True); ns = len(states)
    dedge = fs.edge_density(states)
    base = fc.fl.gen_rules(k_max=2, grid=(0.0, 0.5, 1.0))
    G = np.unique(np.round(np.stack([fc.fl.g_vec(states, k, A, s, p, t) for (k, A, s, p) in base], axis=0), 12), axis=0)
    types = []
    for k in range(2, kmax_gen + 1):
        for (_, A) in fe.enumerate_graphs(k, triangle_free=True):
            E, S, cls = fc.precompute_type(states, k, A); types.append((k, A, E, S, cls))
    SIGS = {"C5": (5, fe.adj_from_edges(5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]))}
    for nm in loc_types:
        sig = SIGS[nm]; E, S, cls = fc.precompute_type(states, *sig); types.append((sig[0], sig[1], E, S, cls))
    print(f"  deficit types ready [{time.time()-t0:.0f}s]", flush=True)
    # moment blocks as flat (t*t, ns) matrices
    Pflats = []
    for (lab, sigma, flags) in fc.moment_types(N):
        mats = fs.P_sigma(N, states, sigma, flags); tt = len(flags)
        # normalize per state like precompute_moments
        from math import comb
        k = sigma[0]; s = flags[0][0] - k if flags else 0
        Pf = np.zeros((tt * tt, ns))
        for hi, (n, _A) in enumerate(states):
            nk = 1
            for i in range(k):
                nk *= (n - i)
            denom = nk * (comb(n - k, s) ** 2) if (nk > 0 and n - k >= s) else 1.0
            Pf[:, hi] = (mats[hi] / (denom if denom > 0 else 1.0)).flatten()
        Pflats.append((lab, tt, Pf))
        print(f"    moment block {lab} t={tt} [{time.time()-t0:.0f}s]", flush=True)
    locs = []
    for nm in loc_types:
        sig = SIGS[nm]
        CONST, GRAD, classes, sup = precompute_localizer_affine(states, sig, t)
        locs.append((nm, sig, CONST, GRAD, sup))
        print(f"  localizer affine [{nm}] |sup|={len(sup)} [{time.time()-t0:.0f}s]", flush=True)
    Mrows = []

    def solve():
        x = cp.Variable(ns, nonneg=True); eta = cp.Variable()
        cons = [cp.sum(x) == 1, dedge @ x >= band[0], dedge @ x <= band[1], G @ x >= eta]
        for (lab, tt, Pf) in Pflats:
            cons.append(cp.reshape(Pf @ x, (tt, tt), order="C") >> 0)
        if Mrows:
            cons.append(_norm_rows(Mrows) @ x >= 0)
        pr = cp.Problem(cp.Maximize(eta), cons)
        val = pr.solve(solver=solver) if solver else pr.solve()
        return val, np.array(x.value).ravel(), pr.status

    v, x, st = solve()
    print(f"  iter0: eta={v:+.7f} ({st})", flush=True)
    for it in range(1, maxit + 1):
        added = 0; newcuts = []
        for (k, A, E, S, cls) in types:
            g, p = fc.separate(E, S, x, t)
            if g < v - tol:
                newcuts.append(fc.cut_from_p(E, S, p, t)); added += 1
        ladded = 0; lmn = 0.0
        for (nm, sig, CONST, GRAD, sup) in locs:
            res = separate_localizer_p(CONST, GRAD, sup, x)
            if res is not None:
                p, lam, w = res; lmn = min(lmn, lam); Q = qmat(p)
                r = np.zeros(ns)
                for hi in sup:
                    r[hi] = float(w @ (CONST[hi] + np.einsum("abcd,cd->ab", GRAD[hi], Q)) @ w)
                Mrows.append(r); ladded += 1
        if added == 0 and ladded == 0:
            print(f"  iter{it}: CONVERGED (loc-eig={lmn:+.2e}) [{time.time()-t0:.0f}s]", flush=True); break
        if newcuts:
            G = np.vstack([G] + newcuts)
        v, x, st = solve()
        print(f"  iter{it}: +{added}d +{ladded}L eta={v:+.7f} ({st}) Leig={lmn:+.1e} [{time.time()-t0:.0f}s]", flush=True)
        if v < -tol:
            print(f"  iter{it}: eta={v:+.7f} < 0 -> CLOSED (conic estimate) at t={t}!", flush=True); break
    print(f"FINAL hybrid N={N} t={t}: eta*={v:+.7f} ({st}) [{time.time()-t0:.0f}s]", flush=True)
    return v


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "audit"
    if mode == "hybrid":
        N = int(sys.argv[2]) if len(sys.argv) > 2 else 9
        t = float(sys.argv[3]) if len(sys.argv) > 3 else T_DEFAULT
        run_hybrid(N=N, t=t)
    elif mode == "run":
        N = int(sys.argv[2]) if len(sys.argv) > 2 else 9
        t = float(sys.argv[3]) if len(sys.argv) > 3 else T_DEFAULT
        run_localized(N=N, t=t)
    elif mode == "psep":
        N = int(sys.argv[2]) if len(sys.argv) > 2 else 9
        t = float(sys.argv[3]) if len(sys.argv) > 3 else T_DEFAULT
        lt = tuple(sys.argv[4].split(",")) if len(sys.argv) > 4 else ("C5",)
        run_localized_psep(N=N, t=t, loc_types=lt)
    else:
        EDGE = (2, fe.adj_from_edges(2, [(0, 1)]))
        NON = (2, [0, 0])
        C5 = (5, fe.adj_from_edges(5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]))
        for name, sig in [("NON(k2)", NON), ("EDGE(k2)", EDGE), ("C5(k5)", C5)]:
            k = sig[0]
            err, nch = audit_fast_vs_slow(sig)
            print(f"[{name}] fast-vs-slow maxerr={err:.2e} over {nch} states (k+4={k+4})", flush=True)
    print("DONE", flush=True)
