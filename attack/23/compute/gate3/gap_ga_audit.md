# Second hostile audit of the gap G-A component ledger

Date: 2026-07-10

Status: **PASS.**  The revised proof in
`compute23/gate3/gap_ga_component_ledger.md` is sound.  The first hostile
audit found a false exceptional-component subclaim; the revised inequality
(4) repairs it.  This audit checks the complete paper proof and exact finite
fixtures.  It does not by itself constitute a Lean formalization.

## Scope and exact statement

The audited statement is the symmetric two-demand lemma.  For a connected
finite simple graph `B`, terminal pairs `(w,x0)` and `(y,z)`, and the cut
condition

```text
[T separates w,x0] + [T separates y,z] <= e_B(delta T),
```

if `P` is a `w`--`x0` geodesic of length `d`, `Q` is a `y`--`z`
geodesic of length `D`, and `s=n-1-d`, then `D<=2s`.

For `|M|=1`, RFC dagger from `lemma_rl_proof.md` is exactly this cut
condition: `e_M(delta T)` is the indicator that the endpoints of the unique
M-edge are separated.  Swapping the two demand pairs gives

```text
d <= 2(n-1-D),
```

which rearranges to

```text
2D <= 2(n-1)-d = 2s+d.
```

Thus the two conclusions are exactly SE1 and SE2.  Theorem 6.1 of
`lemma_rl_proof.md` then gives RL for one internal edge.

## The original failure and its repair

The first version claimed that an exceptional initial-tail component could
have no attachment after the first corridor visit and hence could be assigned
no ridden edge.  That claim is false even under every rooted-instance
restriction.

Take

```text
V(B) = {0,1,2,3,4,5,6}
E(B) = {01,12,23,04,24,15,56}
w=0, x0=3, M={46}
P=(0,1,2,3)
Q=(4,0,1,5,6).
```

The bipartition is `{0,2,5} | {1,3,4,6}`.  Both displayed paths are
geodesics, `d=3`, `D=4`, `B union M` is triangle-free, and all 128 cuts
satisfy RFC dagger.  After deleting `P`, the exceptional initial component
`C={4}` has

```text
A_C={0,2}, l_C=0, h_C=2,
q_C=1, r_C=qexc_C=E_C=0,
R={u_0u_1}.
```

Thus the unused forward attachment at `u_2` exists, and `I_C` is the only
component interval covering the ridden edge.  The old assignment was
impossible.  The revised inequality is tight on the same example:

```text
|R intersect I_C| = 1 = min(c,h_C)-a = q_C.
```

The repaired proof correctly argues as follows.  For an exceptional initial
component, all of its vertices are exactly the initial tail, so
`q_C=|C|=alpha`.  If

```text
min(c,h_C)-a > q_C,
```

then integrality gives `min(c,h_C)-a>=q_C+1`.  Since `a` is an attachment,
`l_C<=a`, while the span bound gives

```text
h_C-a <= h_C-l_C <= q_C+1.
```

Consequently `l_C=a`, `h_C-a=q_C+1`, and `c>=h_C`.  A path from `y`
inside the connected `q_C`-vertex component to a vertex attached at
`u_h_C`, followed by the attachment and `P[u_h_C,u_c]`, has length at most

```text
q_C+c-h_C < q_C+c-a.
```

The right side is exactly the length of the geodesic `y`--`u_c` subpath of
`Q`, a contradiction.  Hence `|R intersect I_C|<=q_C`.  For a final-tail
component the reflected calculation is

```text
|R intersect I_C| <= c-max(a,l_C) <= q_C.
```

This is enough for every assignment of ridden edges, without forbidding
unused attachments.

## Proof-node verdicts

1. **Zero or one common vertex: pass.**  If `Q` misses `P`, its `D+1`
   vertices are among the `s` off-corridor vertices.  If it meets `P` once,
   its other `D` vertices are off-corridor.  These give `D+1<=s` and
   `D<=s`, respectively.

2. **Monotone visits: pass.**  Between consecutive corridor visits `u_i`
   and `u_j`, the `Q` subpath and `P[i,j]` are both geodesics, so its length
   is `|j-i|`.  The same is true from the first to last visit.  Therefore the
   sum of the absolute consecutive changes equals the absolute total change;
   every nonzero change has one sign.  This includes isolated intersections
   and shared whole subpaths.

3. **Component spans: pass.**  A simple path inside a `t_C`-vertex
   component between vertices at the extreme attachments, plus the two
   attachment edges, has length at most `t_C+1`.  The corresponding `P`
   subpath is geodesic, giving `h_C-l_C<=t_C+1`.

4. **Nonbridge implies interval coverage: pass.**  Let the ridden edge be
   `u_{k-1}u_k`.  On any alternate path avoiding it, inspect consecutive
   contacts with `P`.  At the first transition from an index at most `k-1`
   to an index at least `k`, the transition cannot be another edge between
   two `P` vertices: geodesicity forbids corridor chords, and the only
   possible consecutive transition is the deleted edge.  Hence that segment
   has internal vertices in one component of `B-P`, attached on both sides
   of the edge.  If no alternate path exists, the edge is a bridge.  Because
   it lies on both `P` and `Q`, its bridge cut separates both demand pairs,
   contradicting capacity one.

5. **Excursion decomposition: pass.**  Internal vertices between consecutive
   `P` visits form a connected path in `B-P`, hence lie in one component.
   Geodesicity gives excursion length equal to its corridor gap.  Strictly
   increasing visit indices make all gap intervals edge-disjoint; the
   ride/excursion dichotomy makes them disjoint from `R`.  A genuine
   excursion has gap at least two, so `qexc_C=0` really implies `E_C=0`.

6. **Ordinary per-component accounting: pass.**  Assigned rides and all
   excursion gaps through `C` are disjoint subsets of `I_C`, yielding (2).
   Substituting `qexc_C=G_C-E_C` gives (3) whenever
   `qexc_C+r_C>=1`; the final inequality is exactly the integer implication
   `qexc_C+r_C>=1 => 1-qexc_C<=r_C`.

7. **Exceptional components: pass after repair.**  If one exceptional
   component contained both tails, it would contain `y,z` and all its
   vertices would be on `Q`; connectedness supplies a `y`--`z` path of
   length at most `q_C-1`, while `Q` also visits `P` and has length at least
   `q_C`.  Otherwise the repaired initial- or final-tail bound above gives
   `|R_C|<=q_C`, which is (3) because `E_C=r_C=0`.

8. **Global ledger: pass.**  Components partition the vertices off `P`, so
   summing (3) gives `|R|+E<=q+2r`.  The exact path decomposition gives
   `D=q+E+|R|`, while `q+r=s`.  Therefore `D<=2s`.

9. **Symmetry and SE2: pass.**  The cut condition is invariant under
   exchanging the demand pairs.  Applying the same proved lemma with `Q` as
   the first corridor gives the displayed swapped inequality and hence SE2.

No proof node uses bipartiteness, the same-side condition on the M-edge, or
triangle-freeness.  Those hypotheses are needed for the surrounding rooted
problem, but the audited two-demand lemma is genuinely stronger.

## Exact verification results

The stable regression wrapper for the hostile-audit witness is:

```bash
python3 -m pytest compute23/gate3/test_gap_ga_component_ledger.py -q
```

It checks all 128 cuts, bipartiteness, triangle-freeness after adding the
M-edge, both displayed geodesics, the failure of the original subclaim, the
repaired exceptional bound at equality, and both final single-edge laws.

### Original counterexample replay

The exact checker enumerated all cuts and printed:

```text
d,D 3 4
P_Q_geodesic True True
triangle_free_union True
RFC_direct True None symmetric_cut_violations []
old_claim_forward_attachment True
repaired_bound 1 <= 1 <= 1 True
```

Command:

```bash
python3 - <<'PY'
import sys
sys.path.insert(0,'compute23/gate3')
from rl_lib import all_dists, check_rfc_direct, union_triangle_free
n=7
B=[(0,1),(1,2),(2,3),(0,4),(2,4),(1,5),(5,6)]
M=[(4,6)]
w,x0=0,3
P=(0,1,2,3)
Q=(4,0,1,5,6)
dist=all_dists(n,B)
ok,T=check_rfc_direct(n,B,M,w,x0)
cut_bad=[]
for S in range(1<<n):
    eB=sum(((S>>a)&1)!=((S>>b)&1) for a,b in B)
    lhs=(((S>>w)&1)!=((S>>x0)&1))+(((S>>4)&1)!=((S>>6)&1))
    if lhs>eB: cut_bad.append(S)
R={0}; IC=set(range(0,2)); a=0; c=1; h=2; qC=1
print('d,D',dist[w][x0],dist[4][6])
print('P_Q_geodesic',len(P)-1==dist[w][x0],len(Q)-1==dist[4][6])
print('triangle_free_union',union_triangle_free(n,B,M))
print('RFC_direct',ok,T,'symmetric_cut_violations',cut_bad)
print('old_claim_forward_attachment',2>a)
print('repaired_bound',len(R&IC),'<=' ,min(c,h)-a,'<=',qC,
      len(R&IC)<=min(c,h)-a<=qC)
PY
```

### Exhaustive structural harness through n=8

The audit enumerated every connected bipartite `B`, every admissible single
M-edge, every RFC-valid root/stub pair, and every choice of geodesics `P,Q`.
It asserted every proof node: zero/one dispatch, monotonicity, span bound,
ride coverage, excursion decomposition and disjointness, (2), (3), both
exceptional-tail bounds, the final ledger, SE1, and SE2.

```text
instances:          7,796
geodesic P/Q pairs: 29,050
zero intersections: 1,550
one intersection:   9,610
multi intersections:17,890
components checked: 36,112
exceptional:        10,636
old-claim failures: 1,872
revised failures:   0
```

The exact command was:

```bash
python3 - <<'PY'
import sys
sys.path.insert(0, 'compute23/gate3')
from rl_lib import (parse_graph6, adj_masks, all_dists, m_candidates, xor_bits,
                    valid_stub_pairs, gen_bipartite, geodesics_between)
NMAX=8
C=dict(instances=0,path_pairs=0,no_meet=0,one_meet=0,multi_meet=0,
       components=0,exceptional=0,old_claim_failures=0)
for n in range(2,NMAX+1):
  bit=xor_bits(n)
  for line in gen_bipartite(n):
    _,edges=parse_graph6(line); adj=adj_masks(n,edges); dist=all_dists(n,edges)
    mc=m_candidates(n,dist)
    if not mc: continue
    ebase=sum((bit[a]^bit[b] for a,b in edges),start=0*bit[0])
    for y,z in mc:
      sl=ebase-(bit[y]^bit[z])
      if sl.min()<0: continue
      ok=valid_stub_pairs(n,sl)
      for w in range(n):
       for x0 in range(n):
        if not ok[w][x0]: continue
        C['instances']+=1; d=dist[w][x0]; s=n-1-d; D=dist[y][z]
        assert D<=2*s and 2*D<=2*s+d
        for P in geodesics_between(n,adj,dist,w,x0):
          pi={v:i for i,v in enumerate(P)}; PS=set(P)
          comp={}; comps=[]
          for root in range(n):
            if root in PS or root in comp: continue
            cid=len(comps); stack=[root]; comp[root]=cid; vs=[]
            while stack:
              u=stack.pop(); vs.append(u); m=adj[u]
              while m:
                v=(m&-m).bit_length()-1; m&=m-1
                if v not in PS and v not in comp: comp[v]=cid; stack.append(v)
            comps.append(vs)
          A=[]
          for vs in comps:
            aa=set()
            for v in vs:
              m=adj[v]
              while m:
                u=(m&-m).bit_length()-1; m&=m-1
                if u in pi: aa.add(pi[u])
            assert aa and max(aa)-min(aa)<=len(vs)+1
            A.append(aa)
          for Q0 in geodesics_between(n,adj,dist,y,z):
            C['path_pairs']+=1; Q=list(Q0)
            vis=[(i,pi[v]) for i,v in enumerate(Q) if v in pi]
            if len(vis)>=2 and vis[0][1]>vis[-1][1]:
              Q=list(reversed(Q)); vis=[(i,pi[v]) for i,v in enumerate(Q) if v in pi]
            if not vis:
              C['no_meet']+=1; assert D+1<=s; continue
            if len(vis)==1:
              C['one_meet']+=1; assert D<=s; continue
            C['multi_meet']+=1
            inds=[j for _,j in vis]
            assert all(a<b for a,b in zip(inds,inds[1:]))
            assert all(qb-qa==b-a for (qa,a),(qb,b) in zip(vis,vis[1:]))
            R=set(); gaps=[]; E=[0]*len(comps); G=[0]*len(comps); X=[0]*len(comps)
            for (qa,a),(qb,b) in zip(vis,vis[1:]):
              inside=Q[qa+1:qb]
              if qb==qa+1:
                assert b==a+1; R.add(a)
              else:
                assert inside and all(v not in PS for v in inside)
                ids={comp[v] for v in inside}; assert len(ids)==1
                cid=next(iter(ids)); g=b-a
                assert qb-qa==g and len(inside)==g-1
                gaps.append((a,b,cid)); E[cid]+=1; G[cid]+=g; X[cid]+=g-1
            GE=[e for a,b,_ in gaps for e in range(a,b)]
            assert len(GE)==len(set(GE)) and R.isdisjoint(GE)
            RA=[set() for _ in comps]
            for e in R:
              covers=[cid for cid,aa in enumerate(A) if min(aa)<=e<max(aa)]
              assert covers; RA[covers[0]].add(e)
            QS=set(Q)-PS; ic=comp[Q[0]] if Q[0] not in PS else None
            fc=comp[Q[-1]] if Q[-1] not in PS else None
            a0=vis[0][1]; c0=vis[-1][1]
            for cid,vs in enumerate(comps):
              C['components']+=1; lo,hi=min(A[cid]),max(A[cid])
              gapc={e for a,b,j in gaps if j==cid for e in range(a,b)}
              assert RA[cid].isdisjoint(gapc) and len(RA[cid])+G[cid]<=hi-lo
              q=len(set(vs)&QS); r=len(vs)-q
              assert X[cid]==G[cid]-E[cid]
              if X[cid]+r:
                assert len(RA[cid])+E[cid]<=q+2*r
              else:
                C['exceptional']+=1
                assert r==0 and E[cid]==0 and q==len(vs)>0
                assert not (cid==ic and cid==fc)
                RI={e for e in R if lo<=e<hi}
                if cid==ic:
                  assert len(RI)<=min(c0,hi)-a0<=q
                  if any(b>a0 for b in A[cid]): C['old_claim_failures']+=1
                elif cid==fc:
                  assert len(RI)<=c0-max(a0,lo)<=q
                  if any(b<c0 for b in A[cid]): C['old_claim_failures']+=1
                else:
                  raise AssertionError('exceptional component is not a tail')
                assert len(RA[cid])<=q
            q=len(QS); r=s-q; Et=sum(E)
            assert D==q+Et+len(R) and len(R)+Et<=q+2*r
print('STRUCTURAL_AUDIT_OK',C)
PY
```

### General two-demand theorem through n=7

As an independent check of the stronger stated lemma, every connected simple
graph through seven vertices and every unordered pair of terminal pairs was
tested directly against all cuts:

```text
connected graphs:       995
terminal-pair pairs:    211,777
cut-valid configurations:195,011
direct inequalities:    390,022
failures:               0
```

Command:

```bash
python3 - <<'PY'
import subprocess,sys
from itertools import combinations_with_replacement,combinations
sys.path.insert(0,'compute23/gate3')
from rl_lib import parse_graph6, all_dists
GENG='/opt/homebrew/bin/geng'
counts={'graphs':0,'demand_pairs':0,'cut_valid':0,'ineq_checks':0}
for n in range(2,8):
  lines=subprocess.run([GENG,'-q','-c',str(n)],capture_output=True,
                       text=True,check=True).stdout.splitlines()
  pairs=list(combinations(range(n),2))
  for line in lines:
    counts['graphs']+=1
    _,E=parse_graph6(line); dist=all_dists(n,E)
    cap=[sum(((T>>a)&1)!=((T>>b)&1) for a,b in E) for T in range(1<<n)]
    sep={p:[int(((T>>p[0])&1)!=((T>>p[1])&1)) for T in range(1<<n)]
         for p in pairs}
    for p,q in combinations_with_replacement(pairs,2):
      counts['demand_pairs']+=1
      if any(sep[p][T]+sep[q][T]>cap[T] for T in range(1<<n)): continue
      counts['cut_valid']+=1
      d=dist[p[0]][p[1]]; D=dist[q[0]][q[1]]
      assert D<=2*(n-1-d)
      assert d<=2*(n-1-D)
      counts['ineq_checks']+=2
print('GENERAL_TWO_DEMAND_AUDIT_OK',counts)
PY
```

### Existing exact gate-3 fixtures

Commands:

```bash
nice -n 19 python3 compute23/gate3/rl_se_verify.py 9 3
nice -n 19 python3 compute23/gate3/rl_m1_frontier.py 11
```

Results:

```text
SE1 checks:       89,016
SE2 checks:       89,016
G1/MSL checks:   136,712
SE fixture failures: 0

frontier triples through n=11: 57
frontier failures: 0
tight signatures reproduced:
  (s,D,d)=(2,4,4), (3,6,6), (6,8,4), (7,8,2)
```

The exact computations are falsification support.  The PASS verdict rests on
the node-by-node proof above, particularly the repaired exceptional-tail
argument and the symmetric application yielding SE2.
