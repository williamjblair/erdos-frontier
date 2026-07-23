#!/usr/bin/env python3
"""FINAL exact cert assembly + verify (v2, N<=200). Moment block = Q = sum_{c in support} w_c vv_c vv_c^T,
vv_c EXACT (dual_cert_n9 atoms), w_c rationalized. Exact per-state check:
   resid[s] = R_cbh[s] - sum_c w_c a_c[s]  >= 0   for ALL 12172 order-10 states,
   a_c = DT @ b_c,  b_c = fx.moment_cut_exact(Pint_lab, rat(vv_c), denom)   (exact Fraction).
If min resid = -eps < 0, WEAKEN delta by eps (rho += eps): delta_final = delta + eps, must stay < 5e-5.
Q>=0 MANIFEST (w_c>=0, rank-1 sum). Output the cert + a one-command independent verifier for Step-1."""
import pickle, numpy as np, time
from fractions import Fraction as Fr
from math import comb, prod
from scipy.sparse import csr_matrix
import prove_cert as pc
import flag_exact as fx
MAXDEN=10**6
t0=time.time()
C=pc.load(9); moms=C['moments']; states=C['states']; ns=len(states)
d=np.load("c5lift_cache.npz",allow_pickle=True)
D=csr_matrix((d["Dval"],(d["Drow"],d["Dcol"])),shape=(ns,int(d["nJ"]))); nJ=D.shape[1]
# exact D as list of (t, s, Fr)
Dco=D.tocoo(); Dtrip=list(zip(Dco.row.tolist(),Dco.col.tolist(),[Fr(float(v)).limit_denominator(10**6) for v in Dco.data]))
labinfo={}
for (lab,tt,sigma,flags,s,Pf,Pint) in moms:
    k=sigma[0]
    denom=[ (prod(n-i for i in range(k))*comb(n-k,s)**2) if (n-k>=s) else 1 for (n,A) in states]
    denom=[Fr(int(x) if x else 1) for x in denom]
    labinfo[lab]=(Pint,denom,tt)
W=pickle.load(open("moment_gram_w.pkl","rb")); sup=W["support"]; labs=W["atoms_lab"]; vvs=W["atoms_vv"]
supw=[W["w"][i] for i in sup]   # FIX: the support atoms' weights (W['w'] is the full 394-vector)
Rc=pickle.load(open("horn_Rcbh_exact.pkl","rb"))
Rcbh=[Fr(num,den) for (num,den) in Rc["Rcbh"]]
delta=Fr(*Rc["delta"]) if isinstance(Rc["delta"],tuple) else Fr(Rc["delta"][0],Rc["delta"][1])
print(f"support {len(sup)} atoms; delta={float(delta):.6e}; computing exact moment term... [{time.time()-t0:.0f}s]",flush=True)
# moment term over order-10 states: momterm[s] = sum_c w_c a_c[s], a_c = DT @ b_c
momterm=[Fr(0)]*nJ
for ci,(lab,vv,wf) in enumerate(zip(labs,vvs,supw)):
    if wf<=1e-13: continue
    w_c=Fr(float(wf)).limit_denominator(MAXDEN)
    Pint,denom,tt=labinfo[lab]
    vrat=fx.rat_vec(np.asarray(vv),MAXDEN)
    bc=fx.moment_cut_exact(Pint,vrat,denom)   # order-9 exact, list of Fr length ns
    # a_c = DT @ b_c : for each D triple (t,s,coef): a_c[s]+=coef*bc[t]; accumulate w_c*a_c into momterm
    for (t,s,coef) in Dtrip:
        if bc[t]!=0: momterm[s]+= w_c*coef*bc[t]
    if (ci+1)%10==0: print(f"  {ci+1}/{len(sup)} atoms [{time.time()-t0:.0f}s]",flush=True)
resid=[Rcbh[s]-momterm[s] for s in range(nJ)]
mn=min(resid); mns=int(np.argmin([float(r) for r in resid]))
eps=max(Fr(0),-mn)
delta_final=delta+eps
THR=Fr(5,100000)
print(f"EXACT full residual: min={float(mn):.6e} at state {mns}  [{time.time()-t0:.0f}s]",flush=True)
print(f"  weaken eps={float(eps):.3e} -> delta_final={delta_final}={float(delta_final):.7e}",flush=True)
print(f"  delta_final < 5e-5 ? {delta_final<THR}  ; < 1/450 ? {delta_final<Fr(1,450)}",flush=True)
print(f"  => v2 cert {'VALID (N<=200)' if delta_final<THR else 'FAILS threshold'}; n<={int((2/(25*float(delta_final)))**0.5)}",flush=True)
pickle.dump(dict(delta_final=(delta_final.numerator,delta_final.denominator),
                 eps=(eps.numerator,eps.denominator), support=sup, min_resid=(mn.numerator,mn.denominator)),
            open("v2_cert_exact.pkl","wb"))
print("saved v2_cert_exact.pkl",flush=True); print("DONE",flush=True)
