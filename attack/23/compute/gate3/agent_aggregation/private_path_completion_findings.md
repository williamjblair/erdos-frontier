# The private-path completion and the exact sparse/dense dichotomy

Status: **PROVED exact strict-induction reduction; not full BF-RL.**  This
completion converts the whole quadratic objective into the square of one
explicit L1-plus-support parameter.  It is self-tight on long odd cycles
and deliberately noncompetitive on dense distance-four blow-ups, exposing
an exact dense/short complement rather than hiding an aggregation lemma.

## 1. Construction and exact order

Let `(B,M)` be the unrooted part of a valid one-stub instance, and write

```text
D_e = d_B(u,v)  for e=uv in M,
r   = |V(M)|    (the number of distinct M-endpoints),
N_priv = r + sum_{e in M}(D_e-1).
```

Build a new supply graph `H` as follows.

1. Retain one vertex for each distinct endpoint in `V(M)`.
2. For every `e=uv in M`, add a private path of length `D_e` from `u` to
   `v`.  Its `D_e-1` internal vertices occur on no other path.
3. The connected components of the M-graph are also the connected blocks
   of the union of private paths.  Join those blocks in a tree by direct
   B-bridges, using no new vertices.

This has exactly `N_priv` vertices.  Every M-component lies in one side of
the original B-bipartition, since M joins same-side pairs.  Each private path
has even length, so its block is bipartite.  The bipartition of each block
may be flipped independently along the tree of new bridges, making all of
`H` bipartite.

## 2. Flip condition

Fix an arbitrary cut of `H`.  If an M-edge `e=uv` crosses it, the endpoints
of e's private B-path lie on opposite sides.  Therefore at least one edge of
that path crosses.  Private paths are edge-disjoint, so choosing one such
crossing path edge for each crossing M-edge is injective.  Hence

```text
e_M(delta T) <= e_H(delta T).
```

The tree bridges only add supply.  Thus `(H,M)` satisfies the unrooted flip
condition without using multicommodity routing in the original graph.

The cut-count summation landing is kernel checked as
`cutCondition_of_privatePathPayments`.

## 3. Exact distance preservation

The private path for `e` gives `d_H(e)<=D_e`.  Conversely, consider a simple
H-path whose endpoints belong to one M-component.

- It cannot use a bridge joining M-components.  Such a bridge separates the
  component tree, while both endpoints lie on the same side; crossing it
  would force the path to cross it again.
- Every private internal vertex has B-degree two.  Thus whenever the path
  enters one private path, it traverses that entire private path between its
  original endpoints.

Replace each such traversal for `f=ab` by an ambient B-geodesic from `a` to
`b`, also of length `D_f`.  The result is an ambient B-walk of the same
length.  In particular every H-path between the endpoints of `e` has length
at least `d_B(e)=D_e`.  Therefore

```text
d_H(e)=D_e  for every e in M.                           (P1)
```

This also proves triangle-freeness.  A triangle containing one M-edge would
give H-distance at most two, contradicting `D_e>=4`; two- and three-M-edge
triangles use only original M-endpoints and are already excluded in
`B union M`.  New internal vertices are not M-incident.

Thus the private completion is a genuine valid instance and

```text
Gamma(H,M) = Gamma_int(B,M).                            (P2)
```

## 4. Exact RL induction gate

Put `F=rlBudget(s,d)`.  In the strict residual,

```text
F = n^2-(d+1)^2+2s p(d) < n^2.
```

Consequently, if

```text
N_priv^2 <= F,                                          (P3)
```

then automatically `N_priv<n`.  Strict Gamma induction applies to `H`, and
`(P2)` and `(P3)` give RL.  There is no same-order Gamma invocation.

The exact size gate and the final transitivity step are kernel checked as
`privatePathOrder_lt_ambient_of_sq_le_rlBudget` and
`totalCost_le_rlBudget_of_privatePathCompletion`.

Hence a residual counterexample must satisfy the single explicit complement

```text
(r + sum_e(D_e-1))^2 > F.                              (P4)
```

In excess coordinates `D_e=x_e+4`, the order is

```text
N_priv = r + sum_e x_e + 3|M|.                         (P5)
```

Identity `(P5)` is kernel checked as
`privatePathOrder_eq_excess_crossTerm`.  It is the promised cross-term:
joint distance excess, demand multiplicity, and endpoint reuse all appear
with exact coefficients.

## 5. Equality and falsification audit

- Long odd cycle: `|M|=1`, `r=2`, `D=n-1`, so `N_priv=n`.  The construction
  is exactly self-tight and correctly does not invoke strict induction.
- Balanced `C5[q]`: `D=4`, `|M|=q^2`, `r=2q`, so
  `N_priv=3q^2+2q`, deliberately much larger than `5q`.  This is the
  dense/short complement, not a false claimed bound.
- n=8 forced hub: the exact completion has order 9>8.  No vertex-load or
  original-graph path packing is asserted.
- n=12 path-packing witness: the exact completion has order greater than
  12.  Every demand receives fresh capacity, so the killed unit-congestion
  claim is not reused.
- Banked mixed-distance series fixture: distances `(4,6)`, four distinct
  endpoints, hence `N_priv=4+3+5=12`; here `12^2=144<=155=F`, so strict
  Gamma induction really closes this fixture.

`test_private_path_completion.py` constructs all these graphs literally and
checks every cut, all distances, triangle-freeness, exact orders, and the
mixed-fixture budget comparison.  Four tests pass with integer/Boolean
arithmetic.

## 6. Empirical complement profile (not a proof dependency)

An exact random audit on 3,000 connected bipartite samples of orders 14--16
found 154 rooted instances in the strict residual whose selected canonical
root-stub geodesic was all-nonbridge.  The private completion closed 144.
All ten uncovered rootings had only distance-four demands:

```text
n=15, d=5, s=9,
(|M|,r,N_priv,Gamma,F) = (3,6,15,75,207) or (4,6,18,100,207).
```

Thus the observed complement is exactly dense/short and has enormous RL
slack; no random fact is used in the theorem.

## 7. Remaining quantified dense/short lemma

After this reduction, BF-RL is needed only when `(P4)` holds.  Combined with
the quotient-cut theorem, the remaining task is to control dense reuse of
distance-four (or near-four) demands from RFC.  A theorem merely restating
`Gamma<=F` on `(P4)` would not be progress; the useful target must exploit
the exact cross-term `(P5)` and the quotient defect condition `(Q_U)`.
