#!/usr/bin/env python3
"""Precompute k=3 and k=4 moment blocks M^sigma(H) (flags on k+3 / k+2) for the order-9 rank-one moment
cut LP route (GPT Q28). Pickles integer Pint (exact rows) + per-state denom. ~30-60 min in Python."""
import time, pickle
from math import comb
import numpy as np
import flag_engine as fe
import flag_sdp as fs

def build(N=9):
    t0 = time.time()
    states = fe.enumerate_graphs(N, triangle_free=True); ns = len(states)
    K3 = [("3K1", (3, [0, 0, 0])), ("K2K1", (3, fe.adj_from_edges(3, [(0, 1)]))),
          ("P3", (3, fe.adj_from_edges(3, [(0, 1), (1, 2)])))]
    K4 = [("4K1", (4, [0, 0, 0, 0])), ("K2+2K1", (4, fe.adj_from_edges(4, [(0, 1)]))),
          ("2K2", (4, fe.adj_from_edges(4, [(0, 1), (2, 3)]))), ("P3+K1", (4, fe.adj_from_edges(4, [(0, 1), (1, 2)]))),
          ("P4", (4, fe.adj_from_edges(4, [(0, 1), (1, 2), (2, 3)]))), ("K1,3", (4, fe.adj_from_edges(4, [(0, 1), (0, 2), (0, 3)]))),
          ("C4", (4, fe.adj_from_edges(4, [(0, 1), (1, 2), (2, 3), (3, 0)])))]
    blocks = []
    for grp, sflag in [(K3, 6), (K4, 6)]:
        for nm, (k, A) in grp:
            flags = fs.enumerate_flags((k, A), sflag); tt = len(flags)
            mats = fs.P_sigma(N, states, (k, A), flags)
            Pint = [np.rint(m).astype(np.int64) for m in mats]
            s = sflag - k
            denom = []
            for (n, _A) in states:
                nk = 1
                for i in range(k):
                    nk *= (n - i)
                d = nk * (comb(n - k, s) ** 2) if (nk > 0 and n - k >= s) else 1
                denom.append(d)
            Pf = np.stack([mats[i] / (denom[i] if denom[i] else 1.0) for i in range(ns)], axis=0)
            blocks.append(dict(name=nm, k=k, sigma=(k, A), s=s, tt=tt, Pf=Pf, Pint=Pint, denom=denom))
            print(f"  {nm} k={k} tt={tt} [{time.time()-t0:.0f}s]", flush=True)
    with open(f"moments_hi_n{N}.pkl", "wb") as f:
        pickle.dump(dict(blocks=blocks), f, protocol=4)
    print(f"SAVED moments_hi_n{N}.pkl ({len(blocks)} blocks) [{time.time()-t0:.0f}s]", flush=True)

if __name__ == "__main__":
    build(9)
    print("DONE", flush=True)
