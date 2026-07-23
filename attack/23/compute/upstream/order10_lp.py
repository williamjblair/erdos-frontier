#!/usr/bin/env python3
"""DECISIVE Step-2 test: the ORDER-10 marginal-lifted LP. Variables x (1897 order-9 densities), q (12172 order-10
densities), eta. Maximize eta s.t. the order-9 cert rows on x (deficit g.x>=eta, moment m.x>=0), the band, AND the
E10 marginal lift  D q = x, q>=0  (x must be a valid 10-vertex deletion-marginal). The order-9 fooling x*
(eta=+6.49e-5) is L1-distance 0.68 from the marginal polytope, so E10 excludes it. If the lifted eta drops:
  eta < 0  => NO 10-extendable band pseudo-graphon exceeds d_mono=2/25 => band CLOSED (pending exact cert).
  0 <= eta < 6.49e-5 => lift helps but not closing (need C5-diagonal / order-11).
  eta ~ 6.49e-5 => lift doesn't help.
Also optionally adds GPT's C5-diagonal envelope z=gamma.q in [2ac-a^2, (a+b)c-ab] on the band, c=pC5.x.
"""
import numpy as np, sys
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, hstack, vstack, eye, coo_matrix
import prove_cert as pc

LO,HI=0.2486,0.3197

def main():
    C=pc.load(9)
    st,ns,dedge,t,rows,prov,v=pc.cutting_plane(C,maxit=12,target=-1e-6,mom_maxvecs=8,verbose=False)
    print(f"order-9 baseline eta*={v:+.7e}, {len(rows)} cuts",flush=True)
    d=np.load("c5lift_cache.npz",allow_pickle=True)
    D=csr_matrix((d["Dval"],(d["Drow"],d["Dcol"])),shape=(ns,int(d["nJ"]))); nJ=D.shape[1]
    pC5=d["pC5"]; gam=d["gam"]
    # variable layout: [ x(ns) | q(nJ) | eta(1) ]
    nv=ns+nJ+1
    # --- A_ub (<= b_ub) ---
    ub_rows=[]; ub_b=[]
    # band on x:  dedge.x <= hi ;  -dedge.x <= -lo
    r=np.zeros(nv); r[:ns]=dedge; ub_rows.append(r.copy()); ub_b.append(HI)
    r=np.zeros(nv); r[:ns]=-dedge; ub_rows.append(r.copy()); ub_b.append(-LO)
    for i,row in enumerate(rows):
        rr=np.asarray(row,float); r=np.zeros(nv)
        if prov[i][0] in ("deficit","deficit_pmap"):
            r[:ns]=-rr; r[-1]=1.0; ub_rows.append(r); ub_b.append(0.0)   # -g.x + eta <= 0
        else:
            r[:ns]=-rr; ub_rows.append(r); ub_b.append(0.0)              # -m.x <= 0
    A_ub=csr_matrix(np.array(ub_rows)); b_ub=np.array(ub_b)
    # --- A_eq (= b_eq): E10  D q - x = 0  (ns rows); sum x = 1 ---
    # [ -I_ns | D | 0 ] @ var = 0
    negI=coo_matrix((-np.ones(ns),(np.arange(ns),np.arange(ns))),shape=(ns,ns))
    E10=hstack([negI, D, csr_matrix((ns,1))],format="csr")
    sumx=np.zeros((1,nv)); sumx[0,:ns]=1.0
    A_eq=vstack([E10, csr_matrix(sumx)],format="csr")
    b_eq=np.concatenate([np.zeros(ns),[1.0]])
    cobj=np.zeros(nv); cobj[-1]=-1.0  # max eta
    bounds=[(0,None)]*(ns+nJ)+[(None,None)]
    print("solving order-10 lifted LP (highs)...",flush=True)
    res=linprog(cobj,A_ub=A_ub,b_ub=b_ub,A_eq=A_eq,b_eq=b_eq,bounds=bounds,method="highs")
    if not res.success:
        print(f"LP status={res.status} ({res.message})",flush=True)
    else:
        eta=-res.fun
        print(f"\n>>> ORDER-10 lifted eta = {eta:+.7e}   (order-9 was {v:+.7e}; drop = {v-eta:+.3e})",flush=True)
        if eta<0:
            print(f"    >>> eta < 0 : NO 10-extendable band pseudo-graphon has d_mono>2/25 => BAND CLOSED (float).",flush=True)
            print(f"        MUST now build an EXACT rational certificate before claiming closure (8 false closures averted).",flush=True)
        elif eta<v-1e-7:
            print(f"    lift HELPS (eta dropped) but does not close; add C5-diagonal envelope / order-11.",flush=True)
        else:
            print(f"    lift does not move eta.",flush=True)
        x=res.x[:ns]; print(f"    lifted x edge-density mean={float(x@dedge):.5f}, support={(x>1e-7).sum()}",flush=True)
    print("DONE",flush=True)

if __name__=="__main__": main()
