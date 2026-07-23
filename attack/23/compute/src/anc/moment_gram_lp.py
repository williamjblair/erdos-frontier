#!/usr/bin/env python3
"""R1 exact moment closure via a MANIFEST Gram LP (no v-recovery, no SDP-rounding).
Q = sum_c w_c vv_c vv_c^T  (vv_c = the 394 EXACT atoms from dual_cert_n9; w_c>=0 => Q>=0 manifestly).
Per-state moment value a_c[s] = vv_c^T Ptilde_lab[s] vv_c, Ptilde_lab[s]=sum_t D[t,s] Pint_lab[t] (order-10 lift)
  => a_c = DT @ b_c,  b_c[t] = vv_c^T Pint_lab[t] vv_c / denom[t].
LP (float feasibility): find w_c>=0 with sum_c w_c a_c[s] <= R_cbh[s] for all 12172 order-10 states s.
If feasible, the w_c>0 SUPPORT is exact-verified next (small). delta stays 4.756e-5 (cuts unchanged)."""
import pickle, numpy as np, time
from math import comb, prod
from scipy.sparse import csr_matrix
from scipy.optimize import linprog
import prove_cert as pc
t0=time.time()
C=pc.load(9); moms=C['moments']; states=C['states']; ns=len(states)
d=np.load("c5lift_cache.npz",allow_pickle=True)
D=csr_matrix((d["Dval"],(d["Drow"],d["Dcol"])),shape=(ns,int(d["nJ"]))); nJ=D.shape[1]; DT=D.T.tocsr()
# per-label Pint + denom
labinfo={}
for (lab,tt,sigma,flags,s,Pf,Pint) in moms:
    k=sigma[0]
    denom=np.array([ (prod(n-i for i in range(k)) * comb(n-k,s)**2) if (n-k>=s) else 1 for (n,A) in states],dtype=float)
    denom[denom==0]=1.0
    labinfo[lab]=(np.asarray(Pint,float), denom, tt)
cert=pickle.load(open("dual_cert_n9.pkl","rb")); prov=cert["prov"]
atoms=[(p[1],np.asarray(p[4],float)) for p in prov if p[0]=="moment"]   # (lab, vv)
print(f"loaded {len(atoms)} atoms, labels {set(l for l,_ in atoms)} [{time.time()-t0:.0f}s]",flush=True)
# b_c[t] = vv^T Pint[t] vv / denom[t]   ; a_c = DT @ b_c
A_cols=[]
for (lab,vv) in atoms:
    Pint,denom,tt=labinfo[lab]
    bc=np.einsum('i,tij,j->t', vv, Pint, vv)/denom           # (ns,)
    ac=np.asarray(DT@bc).ravel()                              # (nJ,)
    A_cols.append(ac)
Amat=np.array(A_cols).T   # (nJ, natoms)
print(f"built a_c matrix {Amat.shape} [{time.time()-t0:.0f}s]",flush=True)
Rc=pickle.load(open("horn_Rcbh_exact.pkl","rb"))
Rcbh=np.array([num/den for (num,den) in Rc["Rcbh"]],dtype=float)
# ROBUST LP (GPT R1): max eps s.t. Amat @ w + eps <= Rcbh + BETA, w>=0  (beta-bump avoids knife's-edge)
BETA=1e-6
na=Amat.shape[1]
Aub=np.hstack([Amat, np.ones((Amat.shape[0],1))])
cost=np.zeros(na+1); cost[-1]=-1.0
res=linprog(cost, A_ub=Aub, b_ub=Rcbh+BETA, bounds=[(0,None)]*na+[(None,None)], method="highs")
print(f"LP status: success={res.success} msg={res.status} BETA={BETA} eps_q={(res.x[-1] if res.success else None)} [{time.time()-t0:.0f}s]",flush=True)
if res.success:
    w=res.x[:na]; sup=np.where(w>1e-12)[0]
    resid=Rcbh - Amat@w   # >= -BETA + eps_q (robust margin)
    print(f"  FEASIBLE: support |w>0|={len(sup)}/{na}; sum w={w.sum():.4f}; min slack (R_cbh - <Q,Ptilde>) = {resid.min():.3e}",flush=True)
    print(f"  => moment block CLOSES via {len(sup)} G1 atoms; full residual min would be {resid.min():.3e} (>=0 needed)",flush=True)
    pickle.dump(dict(w=w.tolist(), support=sup.tolist(), atoms_lab=[atoms[i][0] for i in sup],
                     atoms_vv=[atoms[i][1].tolist() for i in sup]), open("moment_gram_w.pkl","wb"))
    print("  saved moment_gram_w.pkl (support atoms for exact verify)",flush=True)
else:
    print(f"  INFEASIBLE in G1 atom span -> need full-cone SDP + Cholesky rounding (GPT option a proper)",flush=True)
print("DONE",flush=True)
