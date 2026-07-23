#!/usr/bin/env python3
"""Minimal: ONE C5-diagonal branch [a,b] containing the E10 optimum c~0.0195, sparse-precomputed, highs-ipm.
Decisive read: does the C5-diagonal envelope drop eta on the fooling's own branch?"""
import numpy as np, pickle, sys
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, hstack, vstack, coo_matrix
import prove_cert as pc
LO,HI=0.2486,0.3197
def main():
    a,b=(float(sys.argv[1]),float(sys.argv[2])) if len(sys.argv)>2 else (0.010,0.030)
    C=pc.load(9); ns,dedge,rows,provtypes,v=pickle.load(open("cp_cache.pkl","rb"))
    d=np.load("c5lift_cache.npz",allow_pickle=True)
    D=csr_matrix((d["Dval"],(d["Drow"],d["Dcol"])),shape=(ns,int(d["nJ"]))); nJ=D.shape[1]
    pC5=d["pC5"]; gam=np.asarray(d["gam"],float); nv=ns+nJ+1
    # base ub rows (sparse via coo)
    R=[]; Rb=[]
    def addrow(xpart=None,qpart=None,eta=0.0,rhs=0.0):
        r=np.zeros(nv)
        if xpart is not None: r[:ns]=xpart
        if qpart is not None: r[ns:ns+nJ]=qpart
        r[-1]=eta; R.append(r); Rb.append(rhs)
    addrow(xpart=dedge,rhs=HI); addrow(xpart=-dedge,rhs=-LO)
    for i,row in enumerate(rows):
        if provtypes[i] in ("deficit","deficit_pmap"): addrow(xpart=-row,eta=1.0)
        else: addrow(xpart=-row)
    # C5-diagonal envelope on [a,b] + c in [a,b]
    addrow(xpart=-(a+b)*pC5,qpart=gam,rhs=-a*b)      # z-(a+b)c <= -ab
    addrow(xpart=2*a*pC5,qpart=-gam,rhs=a*a)          # -z+2ac <= a^2
    addrow(xpart=2*b*pC5,qpart=-gam,rhs=b*b)
    addrow(xpart=pC5,rhs=b); addrow(xpart=-pC5,rhs=-a)
    A_ub=csr_matrix(np.array(R)); b_ub=np.array(Rb)
    negI=coo_matrix((-np.ones(ns),(np.arange(ns),np.arange(ns))),shape=(ns,ns))
    E10=hstack([negI,D,csr_matrix((ns,1))],format="csr")
    sumx=np.zeros((1,nv)); sumx[0,:ns]=1.0
    A_eq=vstack([E10,csr_matrix(sumx)],format="csr"); b_eq=np.concatenate([np.zeros(ns),[1.0]])
    cobj=np.zeros(nv); cobj[-1]=-1.0; bounds=[(0,None)]*(ns+nJ)+[(None,None)]
    print(f"solving order-10 + C5-diag on branch c in [{a},{b}] (highs-ipm)...",flush=True)
    res=linprog(cobj,A_ub=A_ub,b_ub=b_ub,A_eq=A_eq,b_eq=b_eq,bounds=bounds,method="highs-ipm")
    if not res.success:
        print(f"status={res.status} ({res.message}) -> branch INFEASIBLE (no x with c in [{a},{b}] survives)",flush=True)
    else:
        eta=-res.fun; x=res.x[:ns]; q=res.x[ns:ns+nJ]
        print(f">>> eta on branch [{a},{b}] = {eta:+.7e}  (E10 was +6.0306e-5, order-9 +6.559e-5)",flush=True)
        print(f"    at opt: c=pC5.x={float(pC5@x):.5e}, z=gamma.q={float(gam@q):.5e}, c^2={(float(pC5@x))**2:.5e}",flush=True)
    print("DONE",flush=True)
if __name__=="__main__": main()
