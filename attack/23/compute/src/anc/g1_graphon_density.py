#!/usr/bin/env python3
"""DEFINITIVE graphon-level soundness test (resolves the finite-vs-limit subtlety the C7[2] finite test exposed).
The cert applies to GRAPHONS (blow-up limit), NOT finite distinct-subset densities. The graphon order-9 density of
a step-graphon W (template T, weights alpha) is computed EXACTLY via COUNT-VECTORS: a multiset (n_0..n_{m-1}) of
how many of the 9 sampled points land in each part (compositions of 9 into m parts), with weight
multinomial(9;n)*prod alpha_i^{n_i}; the induced 9-graph is the T-blow-up with those part-sizes. Then
   m_avg(W) = sum_H p_W(H) * (sum_j gam_j m_j(H)),  g_avg(W)=sum_H p_W(H)*(sum_l lam_l g_l(H)).
Claim: m_avg(W) = sum_sigma ratio_sigma * <Q_sigma, M^sigma(W)>  (ratio: K0=5/126,K1=1/70,EDGE=NON=4/35) >= 0
(by G1: <Q,M> >= 0). This is the cert's ACTUAL transfer object. Verify m_avg>=0, g_avg<=delta, LHS_avg<=delta,
and m_avg == sum ratio<Q,M> (ties to g1_exact_psd). If so: cert SOUND at graphon level; lens-3 + the finite
C7[2] both used the wrong (non-graphon) object.
"""
import pickle, itertools, sys
from fractions import Fraction as F
from math import comb, factorial
import prove_cert as pc, flag_engine as fe

LO=F(1243,5000); HI=F(3197,10000); T=F(2,25)
RATIO={"K0":F(comb(5,4),comb(9,4)),"K1":F(comb(4,4),comb(8,4)),"EDGE":F(comb(4,3),comb(7,3)),"NON":F(comb(4,3),comb(7,3))}

def popcount(x): return bin(x).count("1")
def wl_inv(n,A,rounds=5):
    col=[popcount(A[v]) for v in range(n)]
    for _ in range(rounds):
        newc=[(col[v],tuple(sorted(col[u] for u in range(n) if (A[v]>>u)&1))) for v in range(n)]
        uniq={c:i for i,c in enumerate(sorted(set(newc)))}; col=[uniq[c] for c in newc]
    ep=tuple(sorted((min(col[u],col[v]),max(col[u],col[v])) for u in range(n) for v in range(u+1,n) if (A[u]>>v)&1))
    return (tuple(sorted(col)),ep)

def cyc(m):
    A=[0]*m
    for i in range(m): A[i]|=1<<((i+1)%m); A[i]|=1<<((i-1)%m)
    return A

def blowup_adj(counts, Tadj):
    """9-vertex induced graph: groups per part with given sizes, u~v iff parts T-adjacent."""
    parts=[]
    for p,c in enumerate(counts): parts+=[p]*c
    n=len(parts); A=[0]*n
    for u in range(n):
        for v in range(u+1,n):
            if parts[u]!=parts[v] and (Tadj[parts[u]]>>parts[v])&1: A[u]|=1<<v; A[v]|=1<<u
    return n,A

def compositions(total, parts):
    if parts==1: yield (total,); return
    for first in range(total+1):
        for rest in compositions(total-first, parts-1): yield (first,)+rest

def main():
    C=pc.load(9); states9=C["states"]
    g,m,edens,LHS,mu,nu=pickle.load(open("cert_funcs_n9.pkl","rb"))
    cert=pickle.load(open("dual_cert_n9.pkl","rb")); delta=F(cert["maxPhi_num"],cert["maxPhi_den"])
    # WL match (fast; canonical only for collisions)
    buckets={}
    for i,(n,A) in enumerate(states9): buckets.setdefault(wl_inv(n,A),[]).append(i)
    single={w:l[0] for w,l in buckets.items() if len(l)==1}
    multi={w:[(fe.canonical(9,states9[i][1]),i) for i in l] for w,l in buckets.items() if len(l)>1}
    def match9(A9):
        w=wl_inv(9,A9)
        if w in single: return single[w]
        ck=fe.canonical(9,A9)
        for k,idx in multi[w]:
            if k==ck: return idx
        return -1
    # g1 <Q,M> values per graphon (from g1_exact_psd light sweep, exact-positive): name->{lab:val(float)}
    QM={"C5":{"K0":7.101e-6,"K1":4.501e-5,"EDGE":6.369e-5,"NON":3.680e-4},
        "C7":{"K0":5.379e-6,"K1":6.652e-5,"EDGE":1.944e-5,"NON":1.623e-4}}
    templates=[("C5",5,cyc(5),[F(1,5)]*5),("C7",7,cyc(7),[F(1,7)]*7)]
    for (name,mm,Tadj,alpha) in templates:
        pW={}
        for counts in compositions(9,mm):
            n,A=blowup_adj(counts,Tadj); hi=match9(A)
            if hi<0: raise RuntimeError("blowup not matched")
            w=F(factorial(9))
            for c in counts: w//=factorial(c)
            wt=w
            for p,c in enumerate(counts): wt*= alpha[p]**c
            pW[hi]=pW.get(hi,F(0))+wt
        tot=sum(pW.values())
        g_avg=sum(pW[h]*g[h] for h in pW)
        m_avg=sum(pW[h]*m[h] for h in pW)
        band=sum(pW[h]*(mu*(edens[h]-LO)+nu*(HI-edens[h])) for h in pW)
        lhs=g_avg+m_avg+band
        de=sum(alpha[i]*alpha[j] for i in range(mm) for j in range(mm) if (Tadj[i]>>j)&1)
        qm_id=sum(RATIO[lab]*F(str(QM[name][lab])).limit_denominator(10**9) for lab in RATIO) if name in QM else None
        print(f"\n=== W={name} graphon (d_edge={float(de):.4f}, in-band={LO<=de<=HI}) sum p_W={float(tot):.6f} ===",flush=True)
        print(f"  m_avg (graphon order-9 avg MOMENT) = {float(m_avg):+.6e}   >=0 ? {m_avg>=0}",flush=True)
        if qm_id is not None:
            print(f"  sum_sigma ratio<Q,M>               = {float(qm_id):+.6e}   (matches m_avg ? {abs(float(m_avg-qm_id))<2e-6})",flush=True)
        print(f"  g_avg (graphon avg sum lam g)      = {float(g_avg):+.6e}   <=delta ? {g_avg<=delta}",flush=True)
        print(f"  band_avg                            = {float(band):+.6e}",flush=True)
        print(f"  LHS_avg=g+m+band                    = {float(lhs):+.6e}   <=delta ? {lhs<=delta}",flush=True)
        print(f"  => d_mono(W) <= 2/25 + g_avg <= 2/25+delta : g_avg<=delta is {g_avg<=delta}",flush=True)
    print("\nDONE",flush=True)

if __name__=="__main__": main()
