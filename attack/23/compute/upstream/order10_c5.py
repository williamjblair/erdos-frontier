#!/usr/bin/env python3
"""Add GPT's C5-DIAGONAL envelope to the order-10 marginal lift. Variables x(ns), q(nJ), eta. Base: order-9 cert
rows on x + band + E10 (Dq=x, q>=0). Then enforce t(C5+C5)=t(C5)^2 via the convex envelope on branches of
c = pC5.x in [a,b]:  z=gamma.q,  z <= (a+b)c - ab,  z >= 2ac-a^2,  z >= 2bc-b^2.  Branch c over [cmin,cmax] and
take max eta over branches. Reports z vs c^2 at the E10 optimum (how non-multiplicative it is) and the branched eta.
eta<0 on every branch => band CLOSED (pending exact cert)."""
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, hstack, vstack, coo_matrix
import prove_cert as pc

LO,HI=0.2486,0.3197

def build_base(ns,nJ,dedge,rows,prov,D):
    nv=ns+nJ+1
    ub=[]; ub_b=[]
    r=np.zeros(nv); r[:ns]=dedge; ub.append(r.copy()); ub_b.append(HI)
    r=np.zeros(nv); r[:ns]=-dedge; ub.append(r.copy()); ub_b.append(-LO)
    for i,row in enumerate(rows):
        rr=np.asarray(row,float); r=np.zeros(nv)
        if prov[i][0] in ("deficit","deficit_pmap"): r[:ns]=-rr; r[-1]=1.0
        else: r[:ns]=-rr
        ub.append(r); ub_b.append(0.0)
    negI=coo_matrix((-np.ones(ns),(np.arange(ns),np.arange(ns))),shape=(ns,ns))
    E10=hstack([negI,D,csr_matrix((ns,1))],format="csr")
    sumx=np.zeros((1,nv)); sumx[0,:ns]=1.0
    A_eq=vstack([E10,csr_matrix(sumx)],format="csr"); b_eq=np.concatenate([np.zeros(ns),[1.0]])
    return np.array(ub),np.array(ub_b),A_eq,b_eq,nv

def solve(cobj,A_ub,b_ub,A_eq,b_eq,nv,ns,nJ,extra_ub=None,extra_b=None):
    Aub=A_ub; bub=b_ub
    if extra_ub is not None:
        Aub=np.vstack([A_ub,extra_ub]); bub=np.concatenate([b_ub,extra_b])
    bounds=[(0,None)]*(ns+nJ)+[(None,None)]
    res=linprog(cobj,A_ub=csr_matrix(Aub),b_ub=bub,A_eq=A_eq,b_eq=b_eq,bounds=bounds,method="highs")
    return res

def main():
    C=pc.load(9)
    st,ns,dedge,t,rows,prov,v=pc.cutting_plane(C,maxit=12,target=-1e-6,mom_maxvecs=8,verbose=False)
    d=np.load("c5lift_cache.npz",allow_pickle=True)
    D=csr_matrix((d["Dval"],(d["Drow"],d["Dcol"])),shape=(ns,int(d["nJ"]))); nJ=D.shape[1]
    pC5=d["pC5"]; gam=np.asarray(d["gam"],float)
    A_ub,b_ub,A_eq,b_eq,nv=build_base(ns,nJ,dedge,rows,prov,D)
    # E10 optimum
    cobj=np.zeros(nv); cobj[-1]=-1.0
    res=solve(cobj,A_ub,b_ub,A_eq,b_eq,nv,ns,nJ)
    eta10=-res.fun; x=res.x[:ns]; q=res.x[ns:ns+nJ]
    c_opt=float(pC5@x); z_opt=float(gam@q)
    print(f"E10 eta={eta10:+.7e}; at optimum c=pC5.x={c_opt:.5e}, z=gamma.q={z_opt:.5e}, c^2={c_opt**2:.5e}, z-c^2={z_opt-c_opt**2:+.3e}",flush=True)
    # range of c
    cc=np.zeros(nv); cc[:ns]=pC5
    rmin=solve(cc,A_ub,b_ub,A_eq,b_eq,nv,ns,nJ); cmin=float(pC5@rmin.x[:ns])
    rmax=solve(-cc,A_ub,b_ub,A_eq,b_eq,nv,ns,nJ); cmax=float(pC5@rmax.x[:ns])
    print(f"c=pC5.x range over E10-feasible: [{cmin:.5e}, {cmax:.5e}]",flush=True)
    # branch [cmin,cmax] into K intervals; envelope z<=(a+b)c-ab, z>=2ac-a^2, z>=2bc-b^2
    K=8; edges=np.linspace(max(cmin,0),cmax+1e-9,K+1)
    worst=-1e9
    for bi in range(K):
        a,b=edges[bi],edges[bi+1]
        # z = gamma.q (cols ns..ns+nJ); c = pC5.x (cols :ns)
        eu=[]; eb=[]
        # z <= (a+b)c - ab  ->  z - (a+b)c <= -ab
        r=np.zeros(nv); r[ns:ns+nJ]=gam; r[:ns]-= (a+b)*pC5; eu.append(r.copy()); eb.append(-a*b)
        # z >= 2ac - a^2 -> -z + 2a c <= a^2
        r=np.zeros(nv); r[ns:ns+nJ]=-gam; r[:ns]+=2*a*pC5; eu.append(r.copy()); eb.append(a*a)
        r=np.zeros(nv); r[ns:ns+nJ]=-gam; r[:ns]+=2*b*pC5; eu.append(r.copy()); eb.append(b*b)
        # restrict c to [a,b]: pC5.x <= b ; -pC5.x <= -a
        r=np.zeros(nv); r[:ns]=pC5; eu.append(r.copy()); eb.append(b)
        r=np.zeros(nv); r[:ns]=-pC5; eu.append(r.copy()); eb.append(-a)
        res=solve(cobj,A_ub,b_ub,A_eq,b_eq,nv,ns,nJ,np.array(eu),np.array(eb))
        e=-res.fun if res.success else None
        if e is not None: worst=max(worst,e)
        print(f"  branch c in [{a:.4e},{b:.4e}]: eta={'INFEAS' if e is None else f'{e:+.6e}'}",flush=True)
    print(f"\n>>> ORDER-10 + C5-diagonal: max eta over branches = {worst:+.7e}  (E10 was {eta10:+.7e}, order-9 {v:+.7e})",flush=True)
    if worst<0: print("    >>> eta<0 on ALL branches => BAND CLOSED (float). Build EXACT cert next.",flush=True)
    elif worst<eta10-1e-7: print("    C5-diagonal helps further but does not close.",flush=True)
    else: print("    C5-diagonal does not move eta beyond E10.",flush=True)
    print("DONE",flush=True)

if __name__=="__main__": main()
