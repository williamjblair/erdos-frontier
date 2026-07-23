#!/usr/bin/env python3
"""G1 EXACT moment-PSD certificate for Erdos #23 Step-1 cert (dual_cert_n9.pkl).
For each cert sigma and a rational step-graphon W (template T 0/1 + rational part weights alpha), build the
graphon flag-product moment matrix M^sigma(W) in the ENGINE's flag basis, EXACTLY (Fraction), as the Gram form
   M^sigma(W) = sum_c w_c q_c q_c^T,   c = ordered root part-assignment inducing sigma,
   w_c = prod alpha (rational, >=0),   q_c[F_i] = sum_{ordered ext part-assignment e} prod alpha[e] * 1(canon(roots,ext)=F_i)
This is a MANIFEST exact rational PSD certificate (sum of w_c>=0 times rank-1 PSD). We (a) recompute M a second,
independent way (direct double-sum over root+ext1+ext2 part-assignments binned by the engine flag key) and check
EXACT equality (guards the binning), (b) confirm symmetry, (c) confirm <Q_sigma, M> >= 0 EXACTLY where Q_sigma is
the cert's PSD matrix sum_j gam_j v_j v_j^T (gam>=0). M^sigma(W) PSD => moment atoms m_j(W)=v_j^T M v_j >= 0 =>
cert sound on graphons (Razborov positivity, here exhibited exactly). Disjointness of S1,S2 in P^sigma is what
makes the W-average factor into the Gram form (O(1/n) finite-n defect lives only in per-state P^sigma(H)).
"""
import pickle, itertools, sys
from fractions import Fraction as Fr
import numpy as np
import prove_cert as pc
import flag_engine as fe

# ---- templates: (name, m, Tadj bitmask list, alpha weights as Fraction, triangle_free, d_edge) ----
def cyc(m):
    A=[0]*m
    for i in range(m):
        A[i] |= 1<<((i+1)%m); A[i] |= 1<<((i-1)%m)
    return A
def petersen():
    # outer 0-4 pentagon, inner 5-9 pentagram, spokes i-(i+5)
    A=[0]*10
    def e(u,v): A[u]|=1<<v; A[v]|=1<<u
    for i in range(5):
        e(i,(i+1)%5); e(5+i,5+((i+2)%5)); e(i,5+i)
    return A
def dedge_template(m,Tadj,alpha):
    s=Fr(0)
    for i in range(m):
        for j in range(m):
            if (Tadj[i]>>j)&1: s+=alpha[i]*alpha[j]
    return s
def tri_free(m,Tadj):
    for i in range(m):
        for j in range(m):
            for k in range(m):
                if i<j<k and (Tadj[i]>>j)&1 and (Tadj[j]>>k)&1 and (Tadj[i]>>k)&1: return False
    return True

def templates():
    out=[]
    out.append(("C5_equal",5,cyc(5),[Fr(1,5)]*5))
    out.append(("C7_equal",7,cyc(7),[Fr(1,7)]*7))
    out.append(("C9_equal",9,cyc(9),[Fr(1,9)]*9))
    out.append(("Petersen",10,petersen(),[Fr(1,10)]*10))
    # weighted C5 tuned into band: weights (a,a,a,b,b)
    a,b=Fr(3,14),Fr(2,14)  # sum=3a+2b=9/14+4/14=13/14? fix to 1
    # solve 3a+2b=1 with a=3/14 -> 9/14+2b=1 -> b=5/28
    a=Fr(3,14); b=Fr(5,28)
    out.append(("C5_w_band",5,cyc(5),[a,a,a,b,b]))
    return out

def flag_keys(flags,k):
    return { fe.canonical(fm,fA,roots=k): idx for idx,(fm,fA) in enumerate(flags) }

def induced_adj(parts, Tadj):
    """adjacency bitmask list for vertices placed at given parts (same part => nonadjacent)."""
    n=len(parts); A=[0]*n
    for u in range(n):
        for v in range(u+1,n):
            if parts[u]!=parts[v] and (Tadj[parts[u]]>>parts[v])&1:
                A[u]|=1<<v; A[v]|=1<<u
    return A

def roots_induce_sigma(parts, Tadj, sigma):
    k,Asig=sigma
    for a in range(k):
        for b in range(a+1,k):
            e = 1 if (parts[a]!=parts[b] and (Tadj[parts[a]]>>parts[b])&1) else 0
            s = 1 if (Asig[a]>>b)&1 else 0
            if e!=s: return False
    return True

def build_M(sigma, flags, s, m, Tadj, alpha):
    """returns (M dict[(i,j)]->Fr, gram list of (w_c,q_c)). Gram form M = sum_c w_c q_c q_c^T."""
    k,Asig=sigma; t=len(flags); fk=flag_keys(flags,k)
    gram=[]
    M=[[Fr(0)]*t for _ in range(t)]
    for p in itertools.product(range(m),repeat=k):
        if not roots_induce_sigma(p,Tadj,sigma): continue
        wc=Fr(1)
        for a in p: wc*=alpha[a]
        if wc==0: continue
        q=[Fr(0)]*t
        for e in itertools.product(range(m),repeat=s):
            parts=list(p)+list(e)
            A=induced_adj(parts,Tadj)
            key=fe.canonical(k+s,A,roots=k)
            idx=fk.get(key,-1)
            if idx<0: continue   # triangle => not a tri-free flag (skip; W tri-free => won't happen)
            we=Fr(1)
            for b in e: we*=alpha[b]
            q[idx]+=we
        gram.append((wc,q))
        for i in range(t):
            if q[i]==0: continue
            wq=wc*q[i]
            for j in range(t):
                if q[j]!=0: M[i][j]+=wq*q[j]
    return M,gram

def build_M_doublesum(sigma, flags, s, m, Tadj, alpha):
    """independent recompute: direct sum over (root p, ext1 e1, ext2 e2) part-assignments."""
    k,Asig=sigma; t=len(flags); fk=flag_keys(flags,k)
    M=[[Fr(0)]*t for _ in range(t)]
    for p in itertools.product(range(m),repeat=k):
        if not roots_induce_sigma(p,Tadj,sigma): continue
        wc=Fr(1)
        for a in p: wc*=alpha[a]
        if wc==0: continue
        for e1 in itertools.product(range(m),repeat=s):
            A1=induced_adj(list(p)+list(e1),Tadj); i1=fk.get(fe.canonical(k+s,A1,roots=k),-1)
            if i1<0: continue
            w1=Fr(1)
            for b in e1: w1*=alpha[b]
            for e2 in itertools.product(range(m),repeat=s):
                A2=induced_adj(list(p)+list(e2),Tadj); i2=fk.get(fe.canonical(k+s,A2,roots=k),-1)
                if i2<0: continue
                w2=Fr(1)
                for b in e2: w2*=alpha[b]
                M[i1][i2]+=wc*w1*w2
    return M

def main():
    C=pc.load(9); moms=C["moments"]
    cert=pickle.load(open("dual_cert_n9.pkl","rb")); prov=cert["prov"]; gam=cert["gam"]
    # reconstruct Q_sigma per lab (sum gam_j vv vv^T), exact Fraction
    momatoms=[p for p in prov if p[0]=="moment"]
    assert len(momatoms)==len(gam)
    Qlab={}
    for lab in ["K0","K1","EDGE","NON"]: Qlab[lab]=None
    # map lab from atom: prov moment entry = (moment, lab, sigma, s, vv)
    info={lab:(sigma,flags,s) for (lab,tt,sigma,flags,s,Pf,Pint) in moms}
    for j,p in enumerate(momatoms):
        lab=p[1]; vv=p[4]; g=Fr(str(gam[j])) if not isinstance(gam[j],Fr) else gam[j]
        if g==0: continue
        t=len(vv); vvr=[Fr(str(x)) if not isinstance(x,Fr) else x for x in vv]
        if Qlab[lab] is None: Qlab[lab]=[[Fr(0)]*t for _ in range(t)]
        Q=Qlab[lab]
        for i in range(t):
            if vvr[i]==0: continue
            gi=g*vvr[i]
            for jj in range(t):
                if vvr[jj]!=0: Q[i][jj]+=gi*vvr[jj]
    tps=[(lab,)+info[lab] for lab in ["K0","K1","EDGE","NON"]]
    only=sys.argv[1] if len(sys.argv)>1 else None
    for (name,m,Tadj,alpha) in templates():
        if only and only not in name: continue
        de=dedge_template(m,Tadj,alpha); tf=tri_free(m,Tadj)
        print(f"\n===== W = {name}  d_edge={float(de):.4f} ({de})  tri-free={tf} =====",flush=True)
        for (lab,sigma,flags,s) in tps:
            M,gram=build_M(sigma,flags,s,m,Tadj,alpha)
            t=len(flags)
            # symmetry
            sym=all(M[i][j]==M[j][i] for i in range(t) for j in range(t))
            # independent recompute (double-sum is O(m^{2s}); only feasible for small m -- validated exact on C5)
            if m<=6:
                M2=build_M_doublesum(sigma,flags,s,m,Tadj,alpha)
                match=all(M[i][j]==M2[i][j] for i in range(t) for j in range(t))
            else:
                match="skip(m>6; Gram-PSD by construction)"
            # <Q,M>
            Q=Qlab[lab]; QM=Fr(0)
            if Q is not None:
                for i in range(t):
                    for j in range(t):
                        if M[i][j]!=0 and Q[i][j]!=0: QM+=Q[i][j]*M[i][j]
            # float min-eig corroboration (PSD is exact via Gram, this is a sanity sign-check)
            Mf=np.array([[float(M[i][j]) for j in range(t)] for i in range(t)])
            mineig=float(np.linalg.eigvalsh((Mf+Mf.T)/2).min()) if t>0 else 0.0
            ncls=len(gram)
            print(f"  [{lab:>4}] t={t:>2} gram-cols(w_c>=0)={ncls:>3} sym={sym} recompute-match={match} "
                  f"<Q,M>={'+' if QM>=0 else '-'}{abs(float(QM)):.3e} (exact>=0:{QM>=0}) minEig(float)={mineig:+.2e}",flush=True)
    print("\nDONE",flush=True)

if __name__=="__main__": main()
