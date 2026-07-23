#!/usr/bin/env python3
"""Precompute & pickle all heavy order-N blocks (deficit base+types, moment Pflats, C5 localizer affine)
so confirmation + exact-certificate work loads in seconds instead of re-running the ~440s precompute."""
import sys, time, pickle
from math import comb
import numpy as np
import flag_engine as fe
import flag_sdp as fs
import flag_cutgen as fc
import flag_localizer as floc

def build(N, t=2.0/25, kmax_gen=4):
    t0 = time.time()
    states = fe.enumerate_graphs(N, triangle_free=True); ns = len(states)
    dedge = fs.edge_density(states)
    base = fc.fl.gen_rules(k_max=2, grid=(0.0, 0.5, 1.0))
    Gbase = np.unique(np.round(np.stack([fc.fl.g_vec(states, k, A, s, p, t) for (k, A, s, p) in base], axis=0), 12), axis=0)
    print(f"  base {Gbase.shape} [{time.time()-t0:.0f}s]", flush=True)
    deftypes = []
    for k in range(2, kmax_gen + 1):
        for (_, A) in fe.enumerate_graphs(k, triangle_free=True):
            E, S, cls = fc.precompute_type(states, k, A)
            deftypes.append((k, A, E, S, cls))
    C5 = (5, fe.adj_from_edges(5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]))
    E5, S5, cls5 = fc.precompute_type(states, *C5); deftypes.append((C5[0], C5[1], E5, S5, cls5))
    print(f"  deftypes {len(deftypes)} [{time.time()-t0:.0f}s]", flush=True)
    moments = []
    for (lab, sigma, flags) in fc.moment_types(N, smax=(3 if N >= 10 else None)):
        mats = fs.P_sigma(N, states, sigma, flags); tt = len(flags)
        k = sigma[0]; s = flags[0][0] - k if flags else 0
        Pf = np.zeros((tt * tt, ns))
        for hi, (n, _A) in enumerate(states):
            nk = 1
            for i in range(k):
                nk *= (n - i)
            denom = nk * (comb(n - k, s) ** 2) if (nk > 0 and n - k >= s) else 1.0
            Pf[:, hi] = (mats[hi] / (denom if denom > 0 else 1.0)).flatten()
        # also keep integer P for exact certs
        Pint = [np.rint(m).astype(np.int64) for m in mats]
        moments.append((lab, tt, sigma, flags, s, Pf, Pint))
        print(f"  moment {lab} t={tt} [{time.time()-t0:.0f}s]", flush=True)
    CONST, GRAD, classes5, sup = floc.precompute_localizer_affine(states, C5, t)
    Csup = np.stack([CONST[hi] for hi in sup], axis=0)
    Gsup = np.stack([GRAD[hi] for hi in sup], axis=0)
    print(f"  localizer affine |sup|={len(sup)} [{time.time()-t0:.0f}s]", flush=True)
    blob = dict(N=N, t=t, states=states, dedge=dedge, Gbase=Gbase, deftypes=deftypes,
                moments=moments, C5=C5, classes5=classes5, sup=sup, Csup=Csup, Gsup=Gsup)
    fn = f"cache_n{N}.pkl"
    with open(fn, "wb") as f:
        pickle.dump(blob, f, protocol=4)
    print(f"SAVED {fn} [{time.time()-t0:.0f}s]", flush=True)

if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    build(N)
    print("DONE", flush=True)
