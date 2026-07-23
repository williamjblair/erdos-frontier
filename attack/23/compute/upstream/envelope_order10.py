#!/usr/bin/env python3
"""FINISH path (GPT path A + synthesis rec): full SOUND order-10 envelope =
   moment-only validity + k7 (order-9 x=Dq per-root MaxCut) + k8 (U_8 order-10) + (8,9) Gram-PSD cuts (raised modes).
eta <= min( sum_sigma u7_sigma , sum_R u8_R - 2/25 ); u7<=g_{sigma,c}(x); u8<=L_{R,c}(q); and P_R(q)>=0 (Gram).
The k7 leg caps eta<=~6e-4 immediately; the Gram cuts force q PSD-consistent (a real band graphon has U_7<2/25),
so at the binding q both legs should fall <=0. max eta; eta<=0 => band closed (then EXACT Fraction re-verify).
"""
import os
os.environ.setdefault("OMP_NUM_THREADS","64"); os.environ.setdefault("OPENBLAS_NUM_THREADS","64"); os.environ.setdefault("MKL_NUM_THREADS","64")
import numpy as np, pickle, time, sys
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, vstack
from joblib import Parallel, delayed
import flag_cutgen as fc
from run_k7b import sep_multi, precompute_k7
from cutting_plane_u8 import maxcut_coloring
LO,HI=0.2486,0.3197

def run(maxit=60, tol=1e-9, gram_tol=1e-7, modes=4, method="highs-ipm"):  # IPM 4x faster (few rows, many cols)
    ns,dedge,rows,provtypes,_=pickle.load(open("cp_cache.pkl","rb"))
    C=pickle.load(open("cache_n9.pkl","rb")); states=C["states"]; t=C["t"]; assert len(states)==ns
    d=np.load("c5lift_cache.npz",allow_pickle=True)
    D=csr_matrix((d["Dval"],(d["Drow"],d["Dcol"])),shape=(ns,int(d["nJ"]))); nJ=D.shape[1]; DT=D.T.tocsr()
    De=pickle.load(open("u8_decomp.pkl","rb"));    dec_e=De["decomp"]; nR=De["nR"]
    Da=pickle.load(open("u8_decomp_all.pkl","rb")); dec_a=Da["decomp"]; Rprof=Da["Rprofiles"]
    q0=np.load("witness.npz",allow_pickle=True)["q"]
    dt7=precompute_k7(states); n7=len(dt7)
    mom_idx=[i for i in range(len(rows)) if (provtypes[i][0] if isinstance(provtypes[i],(list,tuple)) else provtypes[i])=='moment']
    print(f"ns={ns} nJ={nJ} n7={n7} nR={nR}; MOMENT-only={len(mom_idx)}; modes={modes} gram_tol={gram_tol}",flush=True)
    nv=nJ+1+n7+nR; ETA=nJ; U7=nJ+1; U8=nJ+1+n7
    dedge_q=np.asarray(DT@dedge).ravel(); sum_q=np.asarray(D.sum(axis=0)).ravel()
    mom_q=[np.asarray(DT@np.asarray(rows[i])).ravel() for i in mom_idx]
    def sprow(dd):
        cols=np.fromiter(dd.keys(),int,len(dd)); data=np.fromiter(dd.values(),float,len(dd))
        return csr_matrix((data,(np.zeros(len(cols),int),cols)),shape=(1,nv))
    static=[]; sb=[]
    static.append(sprow({j:dedge_q[j] for j in range(nJ) if dedge_q[j]})); sb.append(HI)
    static.append(sprow({j:-dedge_q[j] for j in range(nJ) if dedge_q[j]})); sb.append(-LO)
    for vq in mom_q: static.append(sprow({j:-vq[j] for j in range(nJ) if vq[j]})); sb.append(0.0)
    static.append(sprow({ETA:1.0,**{U7+i:-1.0 for i in range(n7)}})); sb.append(0.0)
    static.append(sprow({ETA:1.0,**{U8+i:-1.0 for i in range(nR)}})); sb.append(-2.0/25.0)
    Aeq=sprow({j:sum_q[j] for j in range(nJ) if sum_q[j]}); beq=[1.0]
    cobj=np.zeros(nv); cobj[ETA]=-1.0
    bounds=[(0,None)]*nJ+[(None,None)]+[(0,None)]*(n7+nR)
    env=[]
    def solve():
        A=vstack(static+env,format="csr"); b=np.concatenate([sb,np.zeros(len(env))])
        rr=linprog(cobj,A_ub=A,b_ub=b,A_eq=Aeq,b_eq=beq,bounds=bounds,method=method)
        if (not rr.success or rr.x is None) and method!="highs":
            rr=linprog(cobj,A_ub=A,b_ub=b,A_eq=Aeq,b_eq=beq,bounds=bounds,method="highs")
        if rr.success and rr.x is not None:
            return float(-rr.fun),np.asarray(rr.x[:nJ]),np.asarray(rr.x[U7:U7+n7]),np.asarray(rr.x[U8:U8+nR])
        return None,None,None,None
    def sep_k7(x,q,u7,force=False):
        def one(i,E,S):
            ps,gs=sep_multi(E,S,x,t,1e9,tol,keep=1); res=[]
            for p in ps:
                g=fc.cut_from_p(E,S,p,t); gq=np.asarray(DT@np.asarray(g)).ravel()
                if force or (u7 is not None and u7[i]>float(gq@q)+tol): res.append(gq)
            return i,res
        out=Parallel(n_jobs=48,prefer="threads")(delayed(one)(i,E,S) for i,(k,A,E,S,cls) in enumerate(dt7))
        added=0
        for (i,res) in out:
            for gq in res:
                env.append(sprow({U7+i:1.0,**{int(j):-float(gq[j]) for j in np.nonzero(gq)[0]}})); added+=1
        return added
    def sep_k8(q,u8,force=False):
        W=[dict() for _ in range(nR)]; sup=np.where(q>1e-12)[0]
        for jj in sup:
            qj=float(q[jj])
            for (rid,A,B) in dec_e[jj]:
                key=(A,B) if (len(A),A)<=(len(B),B) else (B,A); W[rid][key]=W[rid].get(key,0.0)+qj/90.0
        cm={}
        for rid in range(nR):
            if not W[rid]: continue
            profs=set(); off={}
            for (a,b),w in W[rid].items():
                profs.add(a); profs.add(b)
                if a!=b: off[(a,b)]=off.get((a,b),0.0)+w
            cm[rid]=maxcut_coloring(list(profs),off)
        acc={rid:{} for rid in cm}
        for jj in range(nJ):
            for (rd,A,B) in dec_e[jj]:
                if rd in cm and cm[rd].get(A,0)==cm[rd].get(B,0): a=acc[rd]; a[jj]=a.get(jj,0)+1
        added=0
        for rid,a in acc.items():
            js=np.fromiter(a.keys(),int,len(a)); cs=np.fromiter(a.values(),float,len(a))/90.0
            L=float(cs@q[js]) if len(js) else 0.0
            if force or (u8 is not None and u8[rid]>L+tol):
                env.append(sprow({U8+rid:1.0,**{int(jj):-float(c) for jj,c in zip(js,cs)}})); added+=1
        return added
    def sep_gram(q):
        """GPT accel: per active root R add the PROJECTION cut <M,P_R(q)> >= 0, M = -P_{R,-} (deepest Frobenius
        separating hyperplane, captures ALL negative curvature in one cut). Track worst normalized lambda_min."""
        acc=[dict() for _ in range(nR)]; sup=np.where(q>1e-13)[0]
        for jj in sup:
            qj=float(q[jj])
            for (rid,A,B) in dec_a[jj]: acc[rid][(A,B)]=acc[rid].get((A,B),0.0)+qj/90.0
        cutM={}; worst=0.0
        for rid in range(nR):
            if not acc[rid]: continue
            profs=sorted(set(tuple(p) for p in Rprof[rid])|set(a for (a,b) in acc[rid])|set(b for (a,b) in acc[rid]))
            idx={p:i for i,p in enumerate(profs)}; m=len(profs); P=np.zeros((m,m))
            for (A,B),w in acc[rid].items(): P[idx[A],idx[B]]+=w
            P=0.5*(P+P.T); pr=float(P.sum())
            ev,V=np.linalg.eigh(P)
            lh = ev[0]/pr if pr>1e-13 else 0.0
            if lh<worst: worst=lh
            neg=[i for i in range(m) if ev[i] < -gram_tol*max(pr,1e-12)]
            if not neg: continue
            Pneg=sum(ev[i]*np.outer(V[:,i],V[:,i]) for i in neg)  # NSD negative part
            M=-Pneg                                               # PSD projection matrix
            cutM[rid]={(profs[a],profs[b]):float(M[a,b]) for a in range(m) for b in range(m) if abs(M[a,b])>1e-12}
        if not cutM: return 0, worst
        coeffs={rid:dict() for rid in cutM}
        for jj in range(nJ):
            for (rd,A,B) in dec_a[jj]:
                Md=cutM.get(rd)
                if Md is not None:
                    v=Md.get((A,B))
                    if v is not None: coeffs[rd][jj]=coeffs[rd].get(jj,0.0)+v
        added=0
        for rid,co in coeffs.items():
            if co: env.append(sprow({int(jj):-vv/90.0 for jj,vv in co.items()})); added+=1
        return added, worst
    quni=np.ones(nJ)/nJ; xuni=np.asarray(D@quni).ravel()
    sep_k7(xuni,quni,None,force=True); sep_k8(quni,None,force=True); sep_k8(q0,None,force=True)
    print(f"seeded {len(env)} cuts; solving...",flush=True)
    eta,q,u7,u8=solve(); print(f"iter0: eta={eta:+.7e}",flush=True)
    if q is None: print("INFEASIBLE iter0"); return
    for it in range(1,maxit+1):
        ts=time.time()
        # IPM returns a DENSE interior q -> sparsify for fast separation (cuts are valid for ANY q; the cutting-plane
        # is robust to which feasible point triggers them). Keep states carrying >=1-eps of the mass.
        qs=q.copy()
        if (q>1e-12).sum()>800:
            order=np.argsort(q)[::-1]; cms=np.cumsum(q[order])
            kkeep=int(np.searchsorted(cms, 1.0-1e-4))+1; thrq=q[order[min(kkeep,nJ-1)]]
            qs=np.where(q>=thrq, q, 0.0); s=qs.sum(); qs=qs/s if s>0 else qs
        x=np.asarray(D@qs).ravel()
        a7=sep_k7(x,qs,u7); a8=sep_k8(qs,u8); ag,worst=sep_gram(qs); added=a7+a8+ag
        if added==0: print(f"CONVERGED it{it}: eta={eta:+.7e} min_lambdahat={worst:+.2e}",flush=True); break
        eta,q,u7,u8=solve()
        if eta is None: print(f"it{it}: INFEASIBLE -> CLOSED(float)",flush=True); break
        nn=thr(eta)
        # PRUNE clearly-slack cuts to keep the LP tractable (re-separation re-adds if a dropped cut re-violates)
        prn=0
        if it>=2 and len(env)>700:
            z=np.zeros(nv); z[:nJ]=q; z[ETA]=eta; z[U7:U7+n7]=u7; z[U8:U8+nR]=u8
            Emat=vstack(env,format="csr"); vals=np.asarray(Emat.dot(z)).ravel()  # e.z ; slack=-e.z>=0
            keep=[env[i] for i in range(len(env)) if vals[i]>=-1e-5]
            prn=len(env)-len(keep); env[:]=keep
        print(f"it{it}: +{a7}k7 +{a8}k8 +{ag}proj -{prn}prune (pool {len(env)}) eta={eta:+.7e} n<={nn} minLh={worst:+.2e} [{time.time()-ts:.0f}s]",flush=True)
        if it%2==0:  # periodic save (resumable; robust to timeout)
            pickle.dump(dict(env=[(e.data.tolist(),e.indices.tolist()) for e in env],eta=float(eta),it=it,nv=nv),
                        open("envelope_order10_state.pkl","wb"),protocol=4)
        if eta<=tol:
            print(f">>> eta<=0 -> CANDIDATE band CLOSURE (k7+k8+gram); saving for EXACT re-verify.",flush=True)
            pickle.dump(dict(env=[(e.data.tolist(),e.indices.tolist()) for e in env],eta=eta),open("envelope_order10_state.pkl","wb"),protocol=4); break
    # FINAL accurate solve (highs-ds) -- IPM iterations are approximate; the exact eta determines N
    print(f"FINAL (IPM approx) eta={eta:+.7e}; running accurate highs-ds...",flush=True)
    A=vstack(static+env,format="csr"); b=np.concatenate([sb,np.zeros(len(env))])
    rr=linprog(cobj,A_ub=A,b_ub=b,A_eq=Aeq,b_eq=beq,bounds=bounds,method="highs-ds")
    if rr.success and rr.x is not None: eta=float(-rr.fun)
    print(f"FINAL order10 eta(ACCURATE)={eta:+.7e}  (band closed iff <=0; N<=180 iff <6.17e-5; n<={thr(eta)})",flush=True)
    return eta

def thr(e):
    import math
    return int(math.floor(math.sqrt(2.0/(25*e)))) if e>0 else 999

if __name__=="__main__":
    print("=== FULL order-10 envelope: moment-only + k7 + k8 U_8 + (8,9) Gram (GPT path A finish) ===",flush=True)
    run(); print("DONE",flush=True)
