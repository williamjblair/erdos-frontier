#!/usr/bin/env python3
"""AUDIT the C5-lift diagnostic's 'x* has no 10-extension' (Dq=x* infeasible) result -- it contradicts the
'x* is a real-graph mixture' note, so verify it is REAL not a bug.
(1) SANITY: a real triangle-free graph G's order-9 density p_G must be 10-extendable (q=p_G^{10}); LP must be FEASIBLE.
(2) x* L1-distance to the deletion-marginal polytope: min ||Dq - x*||_1 s.t. q>=0. If >>0, x* is GENUINELY
    non-10-extendable (real kill); if ~0, the strict-equality infeasibility was numerical (false kill).
Uses cached D from c5lift_cache.npz; rebuilds x* and a real-graph density via the perfect-hash match.
"""
import numpy as np, itertools
from math import comb
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, vstack, hstack, eye
import prove_cert as pc, flag_engine as fe
from c5_lift_diag import key9, xstar  # reuse perfect hash + x* builder

LO,HI=0.2486,0.3197

def load_D():
    d=np.load("c5lift_cache.npz",allow_pickle=True)
    D=csr_matrix((d["Dval"],(d["Drow"],d["Dcol"])),shape=(1897,int(d["nJ"])))
    return D, d["pC5"]

def C7_blowup(t):
    n=7*t; A=[0]*n
    for u in range(n):
        for w in range(u+1,n):
            pu,pw=u//t,w//t
            if pu!=pw and (pw==(pu+1)%7 or pw==(pu-1)%7): A[u]|=1<<w; A[w]|=1<<u
    return n,A

def density9(states9, n, A, keymap):
    cnt=np.zeros(len(states9))
    for S in itertools.combinations(range(n),9):
        B=[0]*9
        for ii,u in enumerate(S):
            for jj,w in enumerate(S):
                if jj>ii and (A[u]>>w)&1: B[ii]|=1<<jj; B[jj]|=1<<ii
        hi=keymap.get(key9(9,B),-1)
        if hi<0: raise RuntimeError("subset unmatched")
        cnt[hi]+=1
    return cnt/cnt.sum()

def feasible(D, target):
    nJ=D.shape[1]
    res=linprog(np.zeros(nJ), A_eq=D, b_eq=target, bounds=[(0,None)]*nJ, method="highs")
    return res.status, res.success

def l1_distance(D, target):
    """min sum(sp+sn) s.t. Dq + sp - sn = target, q>=0, sp,sn>=0."""
    ns,nJ=D.shape
    I=eye(ns,format="csr")
    A=hstack([D, I, -I],format="csr")
    nv=nJ+2*ns
    c=np.concatenate([np.zeros(nJ), np.ones(2*ns)])
    res=linprog(c, A_eq=A, b_eq=target, bounds=[(0,None)]*nv, method="highs")
    return res.fun if res.success else None, res.status

def main():
    C=pc.load(9); states9=C["states"]
    D,pC5=load_D()
    print(f"D shape={D.shape} nnz={D.nnz}; D row min-sum={np.asarray(D.sum(1)).min():.3f} (zero rows => bad)",flush=True)
    keymap={ key9(n,A):i for i,(n,A) in enumerate(states9) }
    # (1) SANITY: real graph C7[2] density -> must be feasible
    n,A=C7_blowup(2); pG=density9(states9,n,A,keymap)
    st,fe_ok=feasible(D,pG)
    print(f"\n(1) SANITY real graph C7[2]: 10-extension LP status={st} success={fe_ok}  (1/optimal=feasible expected)",flush=True)
    l1G,stG=l1_distance(D,pG)
    print(f"    C7[2] L1-distance to marginal polytope = {l1G if l1G is None else f'{l1G:.3e}'} (status {stG})  [should be ~0]",flush=True)
    # (2) x* L1-distance
    st2,ns2,dedge,t,rows,prov,v=pc.cutting_plane(C,maxit=12,target=-1e-6,mom_maxvecs=8,verbose=False)
    eta,xs=xstar(ns2,dedge,rows,prov,(LO,HI))
    st,fe_ok=feasible(D,xs)
    print(f"\n(2) FOOLING x* (eta={eta:+.3e}): 10-extension LP status={st} success={fe_ok}",flush=True)
    l1x,stx=l1_distance(D,xs)
    print(f"    x* L1-distance to marginal polytope = {l1x if l1x is None else f'{l1x:.4e}'} (status {stx})",flush=True)
    if l1x is not None:
        if l1x>1e-4:
            print(f"    >>> x* is GENUINELY non-10-extendable (L1 dist {l1x:.2e} >> 0). The order-10 marginal kills it.",flush=True)
            print(f"        Selective lift REAL: x* fails 10-consistency (not just the C5 diagonal). Next: add E10, re-solve eta.",flush=True)
        else:
            print(f"    >>> L1 dist ~0 => x* IS ~10-extendable; the strict-equality infeasibility was NUMERICAL. Re-examine.",flush=True)
    print("DONE",flush=True)

if __name__=="__main__": main()
