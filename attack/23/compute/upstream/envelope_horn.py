#!/usr/bin/env python3
"""GPT path: order-10 envelope + ROOTED HORN (C5) CP-cone cuts (the cut beyond PSD).
Same LP as envelope_order10 (moment-only + k7 + k8 U_8) but the (8,9) leg uses the rooted Horn inequality
  H_R(A_0..A_4) = sum_{i,j} P_R(A_i,A_j) - 4 sum_i P_R(A_i,A_{i+1}) >= 0   (Motzkin-Straus/C5, graphon-sound)
instead of the frozen PSD-projection cut. H_R is LINEAR in q: H_R = <Hmat, P_R(q)>, Hmat = 1_{5set} - 4*cycle.
The witness violates Horn by -1.0 at 247/260 roots => far deeper than the -0.5 PSD defect the projection cut chases.
max eta; eta<=0 => band closed (then EXACT Fraction re-verify). minLh tracked (no gram cut added) for diagnostics."""
import os
os.environ.setdefault("OMP_NUM_THREADS","64"); os.environ.setdefault("OPENBLAS_NUM_THREADS","48"); os.environ.setdefault("MKL_NUM_THREADS","48")
import numpy as np, pickle, time, sys, itertools
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, vstack
from joblib import Parallel, delayed
import flag_cutgen as fc
from run_k7b import sep_multi, precompute_k7
from cutting_plane_u8 import maxcut_coloring
LO,HI=0.2486,0.3197

def horn_tuples_for_R(P, MAXP=12, KEEP=2, hthr=1e-3):
    """Return up to KEEP most-violated 5-cycles (H/pr < -hthr) as (Hval, [s0..s4]) on the top-MAXP profiles."""
    m=P.shape[0]
    if m<5: return []
    deg=P.sum(1)-np.diag(P); top=list(np.argsort(deg)[::-1][:min(MAXP,m)])
    found=[]
    for sub in itertools.combinations(top,5):
        s=list(sub); tot=P[np.ix_(s,s)].sum()
        best=None; bestc=None
        for perm in itertools.permutations(s[1:]):
            cyc=[s[0]]+list(perm)
            cs=sum(P[cyc[i],cyc[(i+1)%5]] for i in range(5)); H=tot-4*cs
            if best is None or H<best: best=H; bestc=cyc
        if best< -1e-12: found.append((best,bestc))
    found.sort(key=lambda z:z[0])
    return found[:KEEP]

def run(maxit=80, tol=1e-9, modes=4, method="highs-ipm", hthr=1e-3, keep=2):
    ns,dedge,rows,provtypes,_=pickle.load(open("cp_cache.pkl","rb"))
    C=pickle.load(open("cache_n9.pkl","rb")); states=C["states"]; t=C["t"]; assert len(states)==ns
    d=np.load("c5lift_cache.npz",allow_pickle=True)
    D=csr_matrix((d["Dval"],(d["Drow"],d["Dcol"])),shape=(ns,int(d["nJ"]))); nJ=D.shape[1]; DT=D.T.tocsr()
    De=pickle.load(open("u8_decomp.pkl","rb"));    dec_e=De["decomp"]; nR=De["nR"]
    Da=pickle.load(open("u8_decomp_all.pkl","rb")); dec_a=Da["decomp"]; Rprof=Da["Rprofiles"]
    q0=np.load("witness.npz",allow_pickle=True)["q"]
    dt7=precompute_k7(states); n7=len(dt7)
    mom_idx=[i for i in range(len(rows)) if (provtypes[i][0] if isinstance(provtypes[i],(list,tuple)) else provtypes[i])=='moment']
    print(f"ns={ns} nJ={nJ} n7={n7} nR={nR}; MOMENT-only={len(mom_idx)}; HORN cuts hthr={hthr} keep={keep}",flush=True)
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
    def build_PR(q):
        acc=[dict() for _ in range(nR)]; sup=np.where(q>1e-13)[0]
        for jj in sup:
            qj=float(q[jj])
            for (rid,A,B) in dec_a[jj]: acc[rid][(A,B)]=acc[rid].get((A,B),0.0)+qj/90.0
        out=[]
        for rid in range(nR):
            if not acc[rid]: continue
            profs=sorted(set(tuple(p) for p in Rprof[rid])|set(a for (a,b) in acc[rid])|set(b for (a,b) in acc[rid]))
            idx={p:i for i,p in enumerate(profs)}; m=len(profs); P=np.zeros((m,m))
            for (A,B),w in acc[rid].items(): P[idx[A],idx[B]]+=w
            P=0.5*(P+P.T); out.append((rid,profs,P,float(P.sum())))
        return out
    def sep_horn(q):
        """Rooted Horn (C5) CP cuts. Per active root R find most-violated 5-cycles; add <Hmat,P_R(q)> >= 0.
        Also track worst PSD lambda_hat (diagnostic only; no PSD cut added)."""
        PRs=build_PR(q)
        def one(rid,profs,P,pr):
            ev=np.linalg.eigvalsh(P); lh=ev[0]/pr if pr>1e-13 else 0.0
            tups=horn_tuples_for_R(P,hthr=hthr,KEEP=keep)
            cms=[]  # list of cutM dicts (directed-pair -> coeff)
            for (Hval,s) in tups:
                Hmat={}
                for a in s:
                    for b in s: Hmat[(a,b)]=Hmat.get((a,b),0.0)+1.0
                for i in range(5):
                    a,b=s[i],s[(i+1)%5]; Hmat[(a,b)]=Hmat.get((a,b),0.0)-4.0
                cms.append({(profs[a],profs[b]):c for (a,b),c in Hmat.items() if abs(c)>1e-12})
            return rid,lh,cms
        res=Parallel(n_jobs=48,prefer="threads")(delayed(one)(rid,profs,P,pr) for (rid,profs,P,pr) in PRs)
        worst=0.0; cutM={}  # rid -> list of cutM dicts
        for rid,lh,cms in res:
            if lh<worst: worst=lh
            if cms: cutM[rid]=cms
        if not cutM: return 0,worst
        # accumulate each cut's q-coefficients over dec_a
        ncuts={rid:len(cms) for rid,cms in cutM.items()}
        coeffs={(rid,k):dict() for rid,cms in cutM.items() for k in range(len(cms))}
        for jj in range(nJ):
            for (rd,A,B) in dec_a[jj]:
                cms=cutM.get(rd)
                if cms is None: continue
                for k,Md in enumerate(cms):
                    v=Md.get((A,B))
                    if v is not None:
                        co=coeffs[(rd,k)]; co[jj]=co.get(jj,0.0)+v
        added=0
        for key,co in coeffs.items():
            if co: env.append(sprow({int(jj):-vv/90.0 for jj,vv in co.items()})); added+=1
        return added,worst
    quni=np.ones(nJ)/nJ; xuni=np.asarray(D@quni).ravel()
    sep_k7(xuni,quni,None,force=True); sep_k8(quni,None,force=True); sep_k8(q0,None,force=True)
    print(f"seeded {len(env)} cuts; solving...",flush=True)
    eta,q,u7,u8=solve(); print(f"iter0: eta={eta:+.7e}",flush=True)
    if q is None: print("INFEASIBLE iter0"); return
    for it in range(1,maxit+1):
        ts=time.time()
        qs=q.copy()
        if (q>1e-12).sum()>800:
            order=np.argsort(q)[::-1]; cms=np.cumsum(q[order])
            kkeep=int(np.searchsorted(cms, 1.0-1e-4))+1; thrq=q[order[min(kkeep,nJ-1)]]
            qs=np.where(q>=thrq, q, 0.0); s=qs.sum(); qs=qs/s if s>0 else qs
        x=np.asarray(D@qs).ravel()
        a7=sep_k7(x,qs,u7); a8=sep_k8(qs,u8); ah,worst=sep_horn(qs); added=a7+a8+ah
        if added==0: print(f"CONVERGED it{it}: eta={eta:+.7e} minLh={worst:+.2e}",flush=True); break
        eta,q,u7,u8=solve()
        if eta is None: print(f"it{it}: INFEASIBLE -> CLOSED(float)",flush=True); break
        nn=thr(eta)
        prn=0
        if it>=2 and len(env)>900:
            z=np.zeros(nv); z[:nJ]=q; z[ETA]=eta; z[U7:U7+n7]=u7; z[U8:U8+nR]=u8
            Emat=vstack(env,format="csr"); vals=np.asarray(Emat.dot(z)).ravel()
            keep_=[env[i] for i in range(len(env)) if vals[i]>=-1e-5]
            prn=len(env)-len(keep_); env[:]=keep_
        print(f"it{it}: +{a7}k7 +{a8}k8 +{ah}horn -{prn}prune (pool {len(env)}) eta={eta:+.7e} n<={nn} minLh={worst:+.2e} [{time.time()-ts:.0f}s]",flush=True)
        if it%2==0:
            pickle.dump(dict(env=[(e.data.tolist(),e.indices.tolist()) for e in env],eta=float(eta),it=it,nv=nv),
                        open("envelope_horn_state.pkl","wb"),protocol=4)
        if eta<=tol:
            print(f">>> eta<=0 -> CANDIDATE band CLOSURE (k7+k8+HORN); saving for EXACT re-verify.",flush=True)
            pickle.dump(dict(env=[(e.data.tolist(),e.indices.tolist()) for e in env],eta=eta),open("envelope_horn_state.pkl","wb"),protocol=4); break
    print(f"FINAL (IPM approx) eta={eta:+.7e}; running accurate highs-ds...",flush=True)
    A=vstack(static+env,format="csr"); b=np.concatenate([sb,np.zeros(len(env))])
    rr=linprog(cobj,A_ub=A,b_ub=b,A_eq=Aeq,b_eq=beq,bounds=bounds,method="highs-ds")
    if rr.success and rr.x is not None: eta=float(-rr.fun)
    print(f"FINAL horn eta(ACCURATE)={eta:+.7e}  (band closed iff <=0; N<=180 iff <6.17e-5; n<={thr(eta)})",flush=True)
    return eta

def thr(e):
    import math
    return int(math.floor(math.sqrt(2.0/(25*e)))) if e>0 else 999

if __name__=="__main__":
    print("=== order-10 envelope + ROOTED HORN (C5) CP cuts (GPT: the cut beyond PSD) ===",flush=True)
    run(); print("DONE",flush=True)
