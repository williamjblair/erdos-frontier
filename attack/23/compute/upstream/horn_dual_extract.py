#!/usr/bin/env python3
"""STEP 1 of the exact-cert emission: rebuild the order-10 Horn LP from the saved state, solve with CLARABEL,
extract the DUAL (z), and validate the dual-feasibility / certificate structure in FLOAT first (the exact
rationalization follows). Mirrors regen_verify_u7.py's dual logic but for my k7+k8+Horn+moment+band LP.

LP (max eta):  max eta  s.t.  sum_s q_s = 1 (rho),  lo<=dedge.q<=hi (mu_lo,mu_hi),  mom_j.q>=0 (nu_j),
  eta<=sum_sigma u7_sigma (k7 leg),  eta<=sum_R u8_R - 2/25 (k8 leg),  u7<=g7 (cut), u8<=g8 (cut), Horn.q>=0,  q>=0.
The certificate bound: delta = hi*mu_hi - lo*mu_lo + rho - 2/25*<k8-leg dual>  ... extract & report what CLARABEL gives.
"""
import os
os.environ.setdefault("OMP_NUM_THREADS","48"); os.environ.setdefault("OPENBLAS_NUM_THREADS","48")
import numpy as np, pickle, time
import clarabel
from scipy.sparse import csr_matrix, csc_matrix, vstack
LO,HI=0.2486,0.3197
ns,dedge,rows,provtypes,_=pickle.load(open("cp_cache.pkl","rb"))
d=np.load("c5lift_cache.npz",allow_pickle=True)
D=csr_matrix((d["Dval"],(d["Drow"],d["Dcol"])),shape=(ns,int(d["nJ"]))); nJ=D.shape[1]; DT=D.T.tocsr()
De=pickle.load(open("u8_decomp.pkl","rb")); nR=De["nR"]
C=pickle.load(open("cache_n9.pkl","rb")); states=C["states"]
from run_k7b import precompute_k7
n7=len(precompute_k7(states))
mom_idx=[i for i in range(len(rows)) if (provtypes[i][0] if isinstance(provtypes[i],(list,tuple)) else provtypes[i])=='moment']
nv=nJ+1+n7+nR; ETA=nJ; U7=nJ+1; U8=nJ+1+n7
dedge_q=np.asarray(DT@dedge).ravel(); sum_q=np.asarray(D.sum(axis=0)).ravel()
mom_q=[np.asarray(DT@np.asarray(rows[i])).ravel() for i in mom_idx]
def sprow(dd):
    cols=np.fromiter(dd.keys(),int,len(dd)); data=np.fromiter(dd.values(),float,len(dd))
    return csr_matrix((data,(np.zeros(len(cols),int),cols)),shape=(1,nv))
# static rows (track tags)
ub=[]; ubb=[]; tag=[]
ub.append(sprow({j:dedge_q[j] for j in range(nJ) if dedge_q[j]})); ubb.append(HI); tag.append('band_hi')
ub.append(sprow({j:-dedge_q[j] for j in range(nJ) if dedge_q[j]})); ubb.append(-LO); tag.append('band_lo')
for jj,vq in enumerate(mom_q): ub.append(sprow({j:-vq[j] for j in range(nJ) if vq[j]})); ubb.append(0.0); tag.append(('mom',jj))
ub.append(sprow({ETA:1.0,**{U7+i:-1.0 for i in range(n7)}})); ubb.append(0.0); tag.append('k7leg')
ub.append(sprow({ETA:1.0,**{U8+i:-1.0 for i in range(nR)}})); ubb.append(-2.0/25.0); tag.append('k8leg')
nstat=len(ub)
st=pickle.load(open("envelope_horn_state.pkl","rb"))
for ei,(dat,idx) in enumerate(st["env"]):
    ub.append(csr_matrix((np.asarray(dat),(np.zeros(len(dat),int),np.asarray(idx))),shape=(1,nv))); ubb.append(0.0); tag.append(('env',ei))
A_ub=vstack(ub,format="csr"); b_ub=np.asarray(ubb,float); m_ub=A_ub.shape[0]
A_eq=sprow({j:sum_q[j] for j in range(nJ) if sum_q[j]}); b_eq=np.array([1.0])
bnd=[i for i in range(nv) if i!=ETA]; Bbound=csr_matrix((-np.ones(len(bnd)),(np.arange(len(bnd)),np.asarray(bnd))),shape=(len(bnd),nv))
A=vstack([A_ub,A_eq,Bbound],format="csc"); b=np.concatenate([b_ub,b_eq,np.zeros(len(bnd))])
q=np.zeros(nv); q[ETA]=-1.0; P=csc_matrix((nv,nv))
cones=[clarabel.NonnegativeConeT(m_ub), clarabel.ZeroConeT(1), clarabel.NonnegativeConeT(len(bnd))]
print(f"LP {A.shape[0]}x{nv}; state it{st.get('it')} saved eta={st.get('eta'):+.7e}; solving for dual...",flush=True)
s=clarabel.DefaultSettings(); s.verbose=False; s.max_iter=300; s.tol_gap_abs=1e-9; s.tol_gap_rel=1e-9; s.tol_feas=1e-9
t0=time.time(); sol=clarabel.DefaultSolver(P,q,A,b,cones,s).solve(); dt=time.time()-t0
x=np.asarray(sol.x); z=np.asarray(sol.z)
eta=float(x[ETA])
print(f"solved {dt:.0f}s status={sol.status} eta={eta:+.7e}",flush=True)
# dual z: first m_ub = duals on A_ub (>=0), then 1 = eq dual (rho), then bounds
zub=z[:m_ub]; rho=float(z[m_ub])
mu_hi=zub[0]; mu_lo=zub[1]
# per-type sum of k7-cut duals (env rows that are k7 cuts have a +1 on some U7 col) -- check structure
# classify env cuts by which leg-var they touch
k7cuts=[]; k8cuts=[]; horncuts=[]
for ei,(dat,idx) in enumerate(st["env"]):
    idxa=np.asarray(idx)
    if (idxa>=U7).any() and (idxa<U8).any(): k7cuts.append(ei)
    elif (idxa>=U8).any(): k8cuts.append(ei)
    else: horncuts.append(ei)
def zenv(ei): return zub[nstat+ei]
sum_k7=sum(zenv(ei) for ei in k7cuts); sum_k8=sum(zenv(ei) for ei in k8cuts); sum_horn=sum(zenv(ei) for ei in horncuts)
zk7leg=zub[tag.index('k7leg')]; zk8leg=zub[tag.index('k8leg')]
print(f"dual: rho={rho:+.6e} mu_hi={mu_hi:.6e} mu_lo={mu_lo:.6e} | k7leg={zk7leg:.4f} k8leg={zk8leg:.4f}",flush=True)
print(f"  env cuts: {len(k7cuts)} k7, {len(k8cuts)} k8, {len(horncuts)} horn; sum dual k7={sum_k7:.4f} k8={sum_k8:.4f} horn={sum_horn:.4f}",flush=True)
# the certificate delta from band+rho+k8leg const term: eta <= ... ; the k8 leg contributes -2/25 * zk8leg to the bound
delta_dual = HI*mu_hi - LO*mu_lo + rho - (2.0/25.0)*zk8leg
print(f"  delta_dual (HI*mu_hi - LO*mu_lo + rho - 2/25*zk8leg) = {delta_dual:+.7e}  vs eta={eta:+.7e}",flush=True)
print(f"  min dual (should be >=0 for ineq rows): {zub.min():+.3e}",flush=True)
pickle.dump(dict(z=z.tolist(),x=x.tolist(),tag=[str(t) for t in tag],nstat=nstat,m_ub=m_ub,
                 k7cuts=k7cuts,k8cuts=k8cuts,horncuts=horncuts,eta=eta,it=st.get('it')),
            open("horn_dual.pkl","wb"))
print("saved horn_dual.pkl",flush=True); print("DONE",flush=True)
