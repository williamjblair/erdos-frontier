#!/usr/bin/env python3
"""
EXACT (Fraction) regenerators for the contradiction-LP cut families + the rational certificate
combiner. The float LP (HIGHS) identifies which cuts/multipliers are active and gives eta<0; this
module RE-DERIVES every active cut as an exact Fraction functional over all triangle-free states and
verifies the rational combination is < 0 for EVERY state (the all-or-nothing gate). Rationalize the
cut data (profile probs p, eigenvectors v/w) and the dual multipliers FIRST, then regenerate.

All-or-nothing: a closure is only real if certify() returns max_H R(H) < 0 with exact arithmetic.
"""
import itertools
from fractions import Fraction as F
import numpy as np
import flag_engine as fe
import flag_sdp as fs


def gr_exact(states, k, Asig, pmap, t):
    """Exact deficit g_r(H) = (1/(n)_k) sum_{R induces sigma} [ (mono density over non-root pairs) - t ].
    pmap: dict frozenset(subset of range(k)) -> Fraction (side-0 prob). t: Fraction. Returns list[F]."""
    sigma = (k, Asig)
    out = []
    for (n, A) in states:
        if n < 2:
            out.append(F(0)); continue
        adj = [[bool((A[u] >> v) & 1) for v in range(n)] for u in range(n)]
        nk = 1
        for i in range(k):
            nk *= (n - i)
        m = n - k
        Cm2 = m * (m - 1) // 2
        if Cm2 <= 0 or nk == 0:
            out.append(F(0)); continue
        g = F(0)
        for R in itertools.permutations(range(n), k):
            if not fs._induces_sigma_ordered(A, R, sigma):
                continue
            Rset = set(R)
            rest = [w for w in range(n) if w not in Rset]
            q = {}
            for w in rest:
                alpha = frozenset(i for i in range(k) if adj[w][R[i]])
                q[w] = pmap.get(alpha, F(1, 2))
            cm = F(0)
            for ui in range(len(rest)):
                u = rest[ui]; Au = adj[u]
                for vi in range(ui + 1, len(rest)):
                    v = rest[vi]
                    if Au[v]:
                        cm += q[u] * q[v] + (1 - q[u]) * (1 - q[v])
            g += (cm / Cm2 - t)
        out.append(g / nk)
    return out


def Psigma_exact(N, states, sigma, flags):
    """Exact (integer) moment matrices P^sigma(H) (raw counts) — same as fs.P_sigma but integer."""
    mats = fs.P_sigma(N, states, sigma, flags)
    return [np.rint(M).astype(object) for M in mats]   # counts are integers


def moment_cut_exact(Pmats_int, v, norm):
    """Exact v^T P(H) v / norm per state. v: list[Fraction]; norm: Fraction (per-state or scalar list)."""
    t = len(v)
    out = []
    for hi, M in enumerate(Pmats_int):
        s = F(0)
        for a in range(t):
            va = v[a]
            if va == 0:
                continue
            for b in range(t):
                if M[a][b]:
                    s += va * v[b] * int(M[a][b])
        nrm = norm[hi] if isinstance(norm, (list, tuple)) else norm
        out.append(s / nrm if nrm else F(0))
    return out


def rationalize(x, D=10**6):
    """Fixed-denominator rational round(x*D)/D. FIXED D (not limit_denominator) so that sums of many
    such rationals keep denominator dividing a power of D -- no LCM/denominator explosion."""
    return F(int(round(float(x) * D)), D)


def rat_vec(v, D=10**6):
    return [F(int(round(float(x) * D)), D) for x in v]


def localizer_cut_exact(states, sup, sigma, w, p, t):
    """Exact w^T L^{sigma,p}(H) w per state (Fraction). w,p: list[Fraction]; t: Fraction.
    Uses the closed-form T (linear in Q=qmat(p)); L = T/norm; returns list[F] over ALL states (0 off sup)."""
    k, Asig = sigma
    import flag_cutgen as fc
    classes = fc.profile_classes(k, Asig); cidx = {c: i for i, c in enumerate(classes)}
    nc = len(classes)
    # q[a,b] = p_a p_b + (1-p_a)(1-p_b)
    Q = [[p[a] * p[b] + (1 - p[a]) * (1 - p[b]) for b in range(nc)] for a in range(nc)]
    supset = set(sup)
    out = [F(0)] * len(states)
    for hi in sup:
        n, A = states[hi]
        nf = norm_factor_exact(n, k)
        if nf == 0:
            continue
        adj = [[bool((A[u] >> v) & 1) for v in range(n)] for u in range(n)]
        Tww = F(0)
        for R in itertools.permutations(range(n), k):
            if not fs._induces_sigma_ordered(A, R, sigma):
                continue
            Wv = [x for x in range(n) if x not in R]
            if len(Wv) < 4:
                continue
            lab = [cidx[frozenset(i for i in range(k) if adj[x][R[i]])] for x in Wv]
            Acnt = [0] * nc
            for l in lab:
                Acnt[l] += 1
            Eord = [[0] * nc for _ in range(nc)]
            for iu in range(len(Wv)):
                u = Wv[iu]; Au = adj[u]; a = lab[iu]
                for iv in range(len(Wv)):
                    if iv != iu and Au[Wv[iv]]:
                        Eord[a][lab[iv]] += 1
            # H2[a,b] = Q[a,b]*Eord[a,b] - t*Pord[a,b];  Pord[a,b]=Acnt[a]Acnt[b]-d_ab Acnt[a]
            H2 = [[Q[a][b] * Eord[a][b] - t * (Acnt[a] * Acnt[b] - (Acnt[a] if a == b else 0)) for b in range(nc)] for a in range(nc)]
            H0 = F(0)
            for a in range(nc):
                for b in range(nc):
                    H0 += H2[a][b]
            H1 = [sum(H2[a][b] for b in range(nc)) for a in range(nc)]
            # T[a,b] = Aa Ab H0 - 2 Aa H1[b] - 2 Ab H1[a] + 2 H2[a,b] + d_ab(4 H1[a]-Aa H0)
            # accumulate w^T T w directly
            for a in range(nc):
                wa = w[a]
                if wa == 0:
                    continue
                for b in range(nc):
                    wb = w[b]
                    if wb == 0:
                        continue
                    Tab = Acnt[a] * Acnt[b] * H0 - 2 * Acnt[a] * H1[b] - 2 * Acnt[b] * H1[a] + 2 * H2[a][b]
                    if a == b:
                        Tab += 4 * H1[a] - Acnt[a] * H0
                    Tww += wa * wb * Tab
        out[hi] = Tww / nf
    return out


def norm_factor_exact(n, k):
    nk = 1
    for i in range(k):
        nk *= (n - i)
    m = n - k
    f4 = m * (m - 1) * (m - 2) * (m - 3) if m >= 4 else 0
    return nk * f4


def edge_density_exact(states):
    out = []
    for (n, A) in states:
        e = sum(1 for u in range(n) for v in range(u + 1, n) if (A[u] >> v) & 1)
        out.append(F(e, n * (n - 1) // 2) if n >= 2 else F(0))
    return out


def certify(states, terms, band, delta):
    """terms: list of (coeff_F, row_list_F) with coeff>=0; band=(lo_F,hi_F) with multipliers folded in
    via the deficit/moment rows already. Here we just check the assembled certificate:
       R(H) = sum_j coeff_j * row_j(H)  +  mu*(hi - e(H)) + nu*(e(H)-lo) + delta  <= 0  for all H?
    Pass band=(mu,nu,lo,hi) folded separately. Returns (ok, max_R, argmax_index)."""
    mu, nu, lo, hi = band
    edens = edge_density_exact(states)
    worst = (F(-10**9), -1)
    for hi_i in range(len(states)):
        R = delta + mu * (hi - edens[hi_i]) + nu * (edens[hi_i] - lo)
        for (c, row) in terms:
            if c != 0:
                R += c * row[hi_i]
        if R > worst[0]:
            worst = (R, hi_i)
    return (worst[0] < 0, worst[0], worst[1])


if __name__ == "__main__":
    # validate gr_exact vs float g_vec on a few rules
    import flag_localcut as fl
    EDGE = (2, fe.adj_from_edges(2, [(0, 1)]))
    states = fe.enumerate_graphs(7, triangle_free=True)
    k, Asig = EDGE
    classes = [frozenset(), frozenset({0}), frozenset({1})]
    pmap_f = {classes[0]: F(1, 2), classes[1]: F(1, 4), classes[2]: F(3, 4)}
    pmap_x = {c: float(pmap_f[c]) for c in classes}
    t_f = F(2, 25)
    ge = gr_exact(states, k, Asig, pmap_f, t_f)
    gx = fl.g_vec(states, k, Asig, sides=None, pmap=pmap_x, t=2.0 / 25)
    err = max(abs(float(ge[i]) - gx[i]) for i in range(len(states)))
    print(f"gr_exact vs float g_vec maxerr = {err:.2e} over {len(states)} states")
    print("DONE")
