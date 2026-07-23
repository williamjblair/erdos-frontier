#!/usr/bin/env python3
"""GPT Pro's selective (9->10) marginal-lift DIAGNOSTIC for Erdos #23 Step-2 (chat 6a3b5aba).
Tests whether the order-9 fooling optimizer x* admits a 10-vertex extension q (D q = x*, q>=0, sum=1) satisfying
the missing multiplicativity diagonal z = t(C5 join C5) = c^2, c = p_ind(C5,W).
  D_{H,J} = (1/10)|{v in V(J): J-v ~= H}|  (vertex-deletion marginal, T_10 -> T_9)
  gamma_J = |{A subset V(J): |A|=5, J[A]~=C5, J[V\\A]~=C5}| / C(10,5)   (C5 join C5 coefficient)
Solve z_min = min{gamma^T q : Dq=x*, q>=0, sum q=1}, z_max = max{...}. Compare (c*)^2 vs [z_min,z_max].
 (c*)^2 NOT in [z_min,z_max] (or infeasible) => x* killed by the C5 diagonal/10-marginal => route VALIDATED.
 (c*)^2 in [z_min,z_max]               => x* survives the full 10-lift => STOP, move to (c).
Fast C5 test: a 5-vertex induced subgraph of a triangle-free graph is C5 iff it is 2-regular (every vertex deg 2).
"""
import numpy as np, itertools, os, sys
from math import comb
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, vstack
import prove_cert as pc
import flag_engine as fe

def popcount(x): return bin(x).count("1")

def induced_density_C5(n, A):
    """#{5-subsets inducing C5}/C(n,5) via 2-regular test (triangle-free => 2-regular 5-set = C5)."""
    cnt=0; tot=comb(n,5)
    for S in itertools.combinations(range(n),5):
        mask=0
        for v in S: mask|=1<<v
        ok=True
        for v in S:
            if popcount(A[v]&mask)!=2: ok=False;break
        if ok: cnt+=1
    return cnt/tot if tot else 0.0

def gamma_J(A):
    """|{A: |A|=5, J[A]~=C5, J[comp]~=C5}|/C(10,5)."""
    full=(1<<10)-1; cnt=0
    for S in itertools.combinations(range(10),5):
        mask=0
        for v in S: mask|=1<<v
        comp=full&~mask
        ok=True
        for v in S:
            if popcount(A[v]&mask)!=2: ok=False;break
        if ok:
            for v in range(10):
                if (comp>>v)&1 and popcount(A[v]&comp)!=2: ok=False;break
        if ok: cnt+=1
    return cnt/comb(10,5)

def wl_inv(n, A, rounds=5):
    col=[popcount(A[v]) for v in range(n)]
    for _ in range(rounds):
        newc=[(col[v], tuple(sorted(col[u] for u in range(n) if (A[v]>>u)&1))) for v in range(n)]
        uniq={c:i for i,c in enumerate(sorted(set(newc)))}
        col=[uniq[c] for c in newc]
    ep=tuple(sorted((min(col[u],col[v]),max(col[u],col[v])) for u in range(n) for v in range(u+1,n) if (A[u]>>v)&1))
    return (tuple(sorted(col)), ep)

def walkcounts(n, A):
    M=[[1 if (A[u]>>v)&1 else 0 for v in range(n)] for u in range(n)]
    def mm(X,Y): return [[sum(X[i][k]*Y[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
    A2=mm(M,M); A3=mm(A2,M); A4=mm(A3,M)
    return tuple(sorted((sum(A2[v]),sum(A3[v]),sum(A4[v]),A2[v][v],A3[v][v],A4[v][v]) for v in range(n)))

def key9(n, A):  # perfect hash on T_9 (WL + walk counts; verified injective, 0 fe.canonical)
    return (wl_inv(n,A), walkcounts(n,A))

def build(states9):
    cache="c5lift_cache.npz"
    if os.path.exists(cache):
        d=np.load(cache, allow_pickle=True)
        print("loaded c5lift_cache.npz",flush=True)
        return d["Drow"], d["Dcol"], d["Dval"], d["gam"], d["pC5"], int(d["nJ"])
    import time
    # perfect hash on T_9 via (WL + walk counts) -- verified injective, ZERO fe.canonical (which is ~1s/call)
    keymap={ key9(n,A): i for i,(n,A) in enumerate(states9) }
    assert len(keymap)==len(states9), "perfect hash not injective!"
    print(f"T_9 perfect-hash map built ({len(keymap)} keys, no canonical)",flush=True)
    def match9(A9):
        return keymap.get(key9(9,A9), -1)
    g10=fe.enumerate_graphs(10, triangle_free=True); nJ=len(g10)
    print(f"T_10={nJ}; building D, gamma...",flush=True); t0=time.time()
    Drow=[]; Dcol=[]; Dval=[]; gam=np.zeros(nJ)
    for j,(n,A) in enumerate(g10):
        acc={}
        for v in range(10):
            verts=[u for u in range(10) if u!=v]
            m,B=fe.induced(A,verts); hi=match9(B)
            if hi<0: raise RuntimeError(f"J-v not in T_9?! J={j} v={v}")
            acc[hi]=acc.get(hi,0)+1
        for hi,c in acc.items():
            Drow.append(hi); Dcol.append(j); Dval.append(c/10.0)
        gam[j]=gamma_J(A)
        if j%1000==0: print(f"  J {j}/{nJ}  ({time.time()-t0:.0f}s)",flush=True)
    pC5=np.array([induced_density_C5(n,A) for (n,A) in states9])
    np.savez(cache, Drow=np.array(Drow),Dcol=np.array(Dcol),Dval=np.array(Dval),gam=gam,pC5=pC5,nJ=nJ)
    print(f"build done in {time.time()-t0:.0f}s",flush=True)
    return np.array(Drow),np.array(Dcol),np.array(Dval),gam,pC5,nJ

def xstar(ns,dedge,rows,prov,band,locs=None):
    lo,hi=band; nv=ns+1; c=np.zeros(nv); c[-1]=-1.0; A=[];b=[]
    A.append(np.concatenate([-dedge,[0.0]])); b.append(-lo)
    A.append(np.concatenate([dedge,[0.0]]));  b.append(hi)
    for i,row in enumerate(rows):
        r=np.asarray(row,float)
        if prov[i][0] in ("deficit","deficit_pmap"): A.append(np.concatenate([-r,[1.0]])); b.append(0.0)
        else: A.append(np.concatenate([-r,[0.0]])); b.append(0.0)
    for (L,) in (locs or []): A.append(np.concatenate([-L,[0.0]])); b.append(0.0)
    Aeq=[np.concatenate([np.ones(ns),[0.0]])]; beq=[1.0]; bnd=[(0,None)]*ns+[(None,None)]
    r=linprog(c,A_ub=np.array(A),b_ub=np.array(b),A_eq=np.array(Aeq),b_eq=np.array(beq),bounds=bnd,method="highs-ipm")
    if not r.success: r=linprog(c,A_ub=np.array(A),b_ub=np.array(b),A_eq=np.array(Aeq),b_eq=np.array(beq),bounds=bnd,method="highs")
    x=np.maximum(r.x[:ns],0); return -r.fun, x/x.sum()

def solve_z(D, gam, xs, sense):
    nJ=D.shape[1]; ns=D.shape[0]
    Aeq=vstack([D, csr_matrix(np.ones((1,nJ)))]).tocsr()
    beq=np.concatenate([xs,[1.0]])
    cobj = gam if sense=="min" else -gam
    r=linprog(cobj, A_eq=Aeq, b_eq=beq, bounds=[(0,None)]*nJ, method="highs")
    if not r.success: return None, r.status
    return (r.fun if sense=="min" else -r.fun), "ok"

def main():
    C=pc.load(9); states9=C["states"]; ns=len(states9)
    Drow,Dcol,Dval,gam,pC5,nJ=build(states9)
    D=csr_matrix((Dval,(Drow,Dcol)), shape=(ns,nJ))
    print(f"D shape={D.shape} nnz={D.nnz}; gamma range [{gam.min():.4f},{gam.max():.4f}], #gamma>0={int((gam>0).sum())}",flush=True)
    st,ns2,dedge,t,rows,prov,v=pc.cutting_plane(C,maxit=12,target=-1e-6,mom_maxvecs=8,verbose=False)
    # build K2 localizer for edge-pinned variant
    q2=np.zeros(ns)
    for hi,(n,A) in enumerate(states9):
        deg=[popcount(A[u]) for u in range(n)]; E=sum(deg)//2
        M2=comb(E,2)-sum(comb(d,2) for d in deg); q2[hi]=8*M2/(n*(n-1)*(n-2)*(n-3))
    cases=[("baseline full-band", (0.2486,0.3197), None)]
    NB=(0.29,0.31); Lk2=(NB[0]+NB[1])*dedge - q2 - NB[0]*NB[1]
    cases.append(("edge-pinned [0.29,0.31]", NB, [(Lk2,)]))
    for (name,band,locs) in cases:
        eta,xs=xstar(ns,dedge,rows,prov,band,locs)
        cstar=float(xs@pC5); c2=cstar*cstar
        zmin,smin=solve_z(D,gam,xs,"min"); zmax,smax=solve_z(D,gam,xs,"max")
        print(f"\n=== x* = {name}  eta={eta:+.6e} ===",flush=True)
        print(f"  c* = p_ind(C5,x*) = {cstar:.6e}   (c*)^2 = {c2:.6e}",flush=True)
        if zmin is None or zmax is None:
            print(f"  10-extension LP INFEASIBLE (min:{smin} max:{smax}) => x* has NO valid 10-vertex extension",flush=True)
            print(f"  >>> x* KILLED by the order-10 marginal itself. Selective lift VALIDATED.",flush=True)
            continue
        print(f"  z achievable range over 10-extensions: [{zmin:.6e}, {zmax:.6e}]",flush=True)
        inside = (zmin-1e-12) <= c2 <= (zmax+1e-12)
        if not inside:
            gap = (c2-zmax) if c2>zmax else (zmin-c2)
            print(f"  (c*)^2 OUTSIDE [z_min,z_max] by {gap:.3e}  >>> x* KILLED by C5 diagonal. Selective lift VALIDATED.",flush=True)
        else:
            print(f"  (c*)^2 INSIDE [z_min,z_max]  >>> x* SURVIVES the 10-lift + C5 diagonal.",flush=True)
            print(f"      (per GPT firm stopping rule: if survives, move to (c) -- band = sharply isolated open wall)",flush=True)
    print("\nDONE",flush=True)

if __name__=="__main__": main()
