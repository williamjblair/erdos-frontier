#!/usr/bin/env python3
"""CAPSTONE: order-N medium-band closure with an EXACT rational certificate.

Pipeline:
 1. Cutting-plane (exact HIGHS LP; rank-one moment cuts = relaxation of moment-PSD, so LP eta >= SDP eta,
    hence eta<0 here is a RIGOROUS closure modulo float arithmetic) tracking provenance of every cut.
 2. Certificate LP (max c): rational nonneg multipliers alpha (deficit), beta_j (moment v_j), gamma_l
    (localizer w_l,p_l), a,b (band) with  sum coeff*f(H) + a(e-lo) + b(hi-e) + c <= 0  for all H, c>0.
 3. Rationalize surviving multipliers + cut data (binary p exact; eigenvectors v/w -> Fraction).
 4. Regenerate every kept cut EXACTLY (flag_exact) and verify  max_H Phi(H) <= 0  with c>0  (Fraction).

A pass here = the medium band [lo,hi] is closed at t (d_mono* < t) by an exact, machine-checkable proof.
"""
import sys, time, pickle
from math import comb
from fractions import Fraction as F
import numpy as np
import cvxpy as cp
import flag_engine as fe
import flag_cutgen as fc
import flag_localizer as floc
import flag_exact as fx

LO = F(1243, 5000)     # 0.2486
HI = F(3197, 10000)    # 0.3197

def load(N):
    with open(f"cache_n{N}.pkl", "rb") as f:
        return pickle.load(f)

def cutting_plane(C, maxit=120, target=-3e-4, band=(0.2486, 0.3197), tol=1e-7, mom_maxvecs=20, verbose=True):
    states = C["states"]; ns = len(states); dedge = C["dedge"]; t = C["t"]
    deftypes = C["deftypes"]
    moments = C["moments"]                       # (lab, tt, sigma, flags, s, Pf, Pint)
    Pmom = [(lab, tt, Pf.T.reshape(ns, tt, tt), s, sigma) for (lab, tt, sigma, flags, s, Pf, Pint) in moments]
    sup = list(C["sup"]); Csup = C["Csup"]; Gsup = C["Gsup"]
    CONST = {hi: Csup[i] for i, hi in enumerate(sup)}
    GRAD = {hi: Gsup[i] for i, hi in enumerate(sup)}
    C5 = C["C5"]
    # certificate functionals (ALL, with provenance) vs LP rows (G: deficit>=eta ; Mrows: moment/loc>=0)
    cert_rows = []; cert_prov = []
    import itertools
    Gdef = []   # deficit rows for the LP (>= eta)
    seen = set()
    grid = (0.0, 0.5, 1.0)
    base_types = [(0, []), (1, [0]), (2, fe.adj_from_edges(2, [(0, 1)])), (2, [0, 0])]
    for (k, A) in base_types:
        E, S, cls = fc.precompute_type(states, k, A); nc = len(cls)
        for q in itertools.product(grid, repeat=nc):
            row = fc.cut_from_q(E, S, np.array(q), t)
            key = tuple(np.round(row, 9))
            if key in seen:
                continue
            seen.add(key)
            Gdef.append(row)
            pmap = {cls[i]: F(q[i]).limit_denominator(2) for i in range(nc)}
            cert_rows.append(row); cert_prov.append(("deficit_pmap", k, A, pmap))
    Mrows = []
    if verbose: print(f"  base ready: {len(Gdef)} deficit rows; entering loop", flush=True)
    from scipy.optimize import linprog
    lo, hi = band
    def solve():
        # vars v = [x_0..x_{ns-1}, eta]; minimize -eta
        c = np.zeros(ns + 1); c[-1] = -1.0
        Aeq = np.zeros((1, ns + 1)); Aeq[0, :ns] = 1.0; beq = [1.0]
        ub_rows = []; ub_b = []
        ub_rows.append(np.concatenate([-dedge, [0.0]])); ub_b.append(-lo)   # -dedge.x <= -lo
        ub_rows.append(np.concatenate([dedge, [0.0]]));  ub_b.append(hi)    #  dedge.x <= hi
        Gd = np.asarray(Gdef)
        Ag = np.concatenate([-Gd, np.ones((Gd.shape[0], 1))], axis=1)        # -g.x + eta <= 0
        if Mrows:
            Mn = floc._norm_rows(Mrows)
            Am = np.concatenate([-Mn, np.zeros((Mn.shape[0], 1))], axis=1)   # -m.x <= 0
            A_ub = np.vstack([np.array(ub_rows), Ag, Am])
        else:
            A_ub = np.vstack([np.array(ub_rows), Ag])
        b_ub = np.array(ub_b + [0.0] * (A_ub.shape[0] - 2))
        bounds = [(0, None)] * ns + [(None, None)]
        r = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=Aeq, b_eq=beq, bounds=bounds, method="highs-ipm")
        if not r.success or r.x is None:
            r = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=Aeq, b_eq=beq, bounds=bounds, method="highs")
        if not r.success or r.x is None:
            return 0.0, np.ones(ns) / ns
        return -float(r.fun), np.asarray(r.x[:ns])
    v, x = solve(); t0 = time.time()
    if verbose: print(f"  first solve done eta={v:+.7f}", flush=True)
    for it in range(1, maxit + 1):
        ta = time.time()
        if verbose: print(f"  it{it} >def", flush=True)
        added = 0
        for (k, A, E, S, cls) in deftypes:
            g, p = fc.separate(E, S, x, t, exhaustive_max=13)
            if g < v - tol:
                row = fc.cut_from_p(E, S, p, t)
                Gdef.append(row)
                cert_rows.append(row); cert_prov.append(("deficit", k, A, tuple(cls), tuple(int(pp) for pp in p)))
                added += 1
        tb = time.time()
        if verbose: print(f"  it{it} >mom (def={tb-ta:.1f}s)", flush=True)
        madded = 0; mn = 0.0
        for (lab, tt, P, s, sigma) in Pmom:
            mrows, lam, vecs = fc.separate_moment(P, x, maxvecs=mom_maxvecs); mn = min(mn, lam)
            for r, vv in zip(mrows, vecs):
                Mrows.append(r); cert_rows.append(r); cert_prov.append(("moment", lab, sigma, s, vv.copy())); madded += 1
        tc = time.time()
        if verbose: print(f"  it{it} >loc (mom={tc-tb:.1f}s)", flush=True)
        ladded = 0; lmn = 0.0
        res = floc.separate_localizer_p(CONST, GRAD, sup, x)
        if res is not None:
            pL, lam, w = res; lmn = lam; Q = floc.qmat(pL); r = np.zeros(ns)
            for hi in sup:
                r[hi] = float(w @ (CONST[hi] + np.einsum("abcd,cd->ab", GRAD[hi], Q)) @ w)
            Mrows.append(r); cert_rows.append(r); cert_prov.append(("localizer", C5, w.copy(), pL.copy())); ladded += 1
        td = time.time()
        if verbose: print(f"  it{it} >lp (loc={td-tc:.1f}s)", flush=True)
        if added == 0 and madded == 0 and ladded == 0:
            if verbose: print(f"  it{it}: CONVERGED eta={v:+.7f}", flush=True); break
        v, x = solve()
        te = time.time()
        if verbose:
            print(f"  it{it}: +{added}d+{madded}m+{ladded}L eta={v:+.7f} cuts={len(cert_rows)} meig={mn:+.1e} Leig={lmn:+.1e} | def={tb-ta:.1f} mom={tc-tb:.1f} loc={td-tc:.1f} lp={te-td:.1f}s", flush=True)
        if v < target:
            if verbose: print(f"  it{it}: eta={v:+.7f} <= target -> stop", flush=True); break
    return states, ns, dedge, t, cert_rows, cert_prov, v

def certificate_lp(rows, dedge, ns, band=(0.2486, 0.3197), verbose=True):
    """max c s.t. for all H: sum coeff_i rows_i(H) + a(e-lo)+b(hi-e)+c <= 0 ; coeff,a,b>=0 ; c<=1."""
    from scipy.optimize import linprog
    nr = len(rows); R = np.array(rows); lo, hi = band                  # R: (nr, ns)
    # vars = [coeff(nr), a, b, c]; minimize -c
    cobj = np.zeros(nr + 3); cobj[-1] = -1.0
    A_ub = np.zeros((ns + 1, nr + 3))
    A_ub[:ns, :nr] = R.T
    A_ub[:ns, nr] = dedge - lo
    A_ub[:ns, nr + 1] = hi - dedge
    A_ub[:ns, nr + 2] = 1.0
    A_ub[ns, nr + 2] = 1.0          # c <= 1
    b_ub = np.zeros(ns + 1); b_ub[ns] = 1.0
    bounds = [(0, None)] * nr + [(0, None), (0, None), (None, None)]
    r = linprog(cobj, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method="highs")
    val = -float(r.fun) if r.success else -1.0
    if verbose: print(f"  certificate LP: max c = {val:+.6e}  ({'success' if r.success else r.message})", flush=True)
    if not r.success:
        return val, np.zeros(nr), 0.0, 0.0, 0.0
    return val, r.x[:nr], float(r.x[nr]), float(r.x[nr + 1]), float(r.x[nr + 2])

def build_and_verify(C, states, prov, coeff, a, b, c, maxden=10**6, keep_tol=1e-9, verbose=True):
    """Rationalize kept cuts + multipliers, regenerate EXACT, verify max_H Phi(H) <= 0 with c>0."""
    t = F(2, 25)
    moments = {lab: (Pint, s, sigma) for (lab, tt, sigma, flags, s, Pf, Pint) in
               [(m[0], m[1], m[2], m[3], m[4], m[5], m[6]) for m in C["moments"]]}
    sup = list(C["sup"])
    edens = fx.edge_density_exact(states)
    keep = [i for i in range(len(coeff)) if coeff[i] > keep_tol]
    if verbose: print(f"  kept {len(keep)}/{len(coeff)} cuts (coeff>{keep_tol})", flush=True)
    Phi = [F(0)] * len(states)
    # band + c
    a_f = fx.rationalize(a, maxden); b_f = fx.rationalize(b, maxden); c_f = fx.rationalize(c, maxden)
    for hi_i in range(len(states)):
        Phi[hi_i] += a_f * (edens[hi_i] - LO) + b_f * (HI - edens[hi_i]) + c_f
    for idx in keep:
        cf = fx.rationalize(coeff[idx], maxden)
        pr = prov[idx]
        if pr[0] == "deficit":
            _, k, A, cls, p = pr
            pmap = {cls[i]: F(int(p[i])) for i in range(len(cls))}
            vals = fx.gr_exact(states, k, A, pmap, t)
        elif pr[0] == "deficit_pmap":
            _, k, A, pmap = pr
            vals = fx.gr_exact(states, k, A, pmap, t)
        elif pr[0] == "moment":
            _, lab, sigma, s, vv = pr
            Pint, ss, sg = moments[lab]
            denom = []
            for (n, _A) in states:
                nk = 1
                for i in range(sigma[0]):
                    nk *= (n - i)
                d = nk * (comb(n - sigma[0], s) ** 2) if (nk > 0 and n - sigma[0] >= s) else 1
                denom.append(F(int(d)) if d else F(1))
            vrat = fx.rat_vec(vv, maxden)
            vals = fx.moment_cut_exact(Pint, vrat, denom)
        else:  # localizer
            _, sg, w, pL = pr
            wrat = fx.rat_vec(w, maxden); prat = fx.rat_vec(pL, maxden)
            vals = fx.localizer_cut_exact(states, sup, sg, wrat, prat, t)
        for hi_i in range(len(states)):
            if vals[hi_i] != 0:
                Phi[hi_i] += cf * vals[hi_i]
    mx = max(Phi); arg = int(np.argmax([float(p) for p in Phi]))
    ok = (mx <= 0) and (c_f > 0)
    if verbose:
        print(f"  EXACT: max_H Phi(H) = {float(mx):+.6e}  (c={float(c_f):.6e})  -> {'CERTIFIED' if ok else 'FAIL'}", flush=True)
        print(f"         argmax state index {arg}", flush=True)
    return ok, mx, c_f

if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    C = load(N)
    print(f"=== order-{N} medium-band closure + exact certificate (t=2/25) ===", flush=True)
    states, ns, dedge, t, rows, prov, v = cutting_plane(C)
    print(f"cutting-plane done: eta*={v:+.7f}, {len(rows)} cuts", flush=True)
    if v >= 0:
        print("eta >= 0: NOT closed by this cut set; abort certificate.", flush=True); sys.exit(0)
    cval, coeff, a, b, c = certificate_lp(rows, dedge, ns)
    if cval <= 0:
        print("certificate LP max c <= 0: cuts insufficient.", flush=True); sys.exit(0)
    with open(f"certdata_n{N}.pkl", "wb") as f:
        pickle.dump(dict(prov=prov, coeff=coeff, a=a, b=b, c=c, rows=rows), f, protocol=4)
    print(f"saved certdata_n{N}.pkl", flush=True)
    ok, mx, c_f = build_and_verify(C, states, prov, coeff, a, b, c)
    print(f"RESULT: {'EXACT CERTIFICATE VERIFIED' if ok else 'certificate verification FAILED'} (max Phi={float(mx):+.3e})", flush=True)
    print("DONE", flush=True)
