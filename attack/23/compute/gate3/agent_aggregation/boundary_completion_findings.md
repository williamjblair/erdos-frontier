# A distance-preserving smaller completion for every off-corridor component

Status: **PROVED conditional reduction to strict Gamma induction.**  The
construction applies to every off-corridor component containing internal
M-edges.  It gives an explicit simple bipartite completion rather than
invoking Gamma on the generally invalid restriction `B[C]`.  The remaining
issue is quantitative: the completion is useful when its explicit order is
strictly smaller and its square fits the global RL budget.

## Statement

Fix a root-stub geodesic `P` in a valid one-stub instance and an
off-corridor component `C` of order `q`.  Let `A_C` be the multiset of B
attachment edges from `C` to `P` (edges, not merely distinct attachment
vertices), and put `a=|A_C|`.

Let `M_C` be the internal M-edges with both endpoints in `C`, and put

```text
Delta = max { d_{B[C]}(u,v) : uv in M_C },   K=Delta/2.
```

All displayed distances are even.  Two-color `C`, and let `a_0,a_1` count
attachment edges by the bipartition side of their C endpoint.  There is an
explicit simple connected bipartite graph `H_C` on

```text
N_C = q + 1 + a(K-1) + min(a_0,a_1)
```

vertices such that:

1. `(H_C,M_C)` satisfies the unrooted flip condition;
2. `H_C union M_C` is triangle-free; and
3. for every `uv in M_C`,
   `d_{H_C}(u,v)=d_{B[C]}(u,v)>=d_B(u,v)`.

Consequently, if `N_C<=n-1`, strict Gamma induction gives the legitimate
local estimate

```text
sum_{uv in M_C} (d_B(u,v)+1)^2 <= N_C^2.               (BC)
```

## Construction

Add one new root `r`.  For every attachment **edge** `e=c u_j` in `A_C`,
add a private path (a spoke) from `c` to `r`; different paths share only
their endpoint `r` and may share `c` when a component vertex has two P
neighbours.  Retain `B[C]` and `M_C`.

Choose the bipartition side of `r` optimally.  A spoke from a C endpoint has
length `K` when that parity reaches `r`, and length `K+1` otherwise.
Choosing the root side so that the majority attachment side uses length `K`
gives exactly `min(a_0,a_1)` long spokes and the displayed order.  Every
spoke has length at least `K`; its parity makes the C bipartition extend to
the common root.  The graph is simple even when two attachments have the
same C endpoint, because their internal spoke vertices are private.

## Cut validity

First isolate the exact boundary inequality.  For every `T subseteq C`, old
RFC at `T` reads

```text
e_{M_C}(delta T)
  + (# M-edges from T to V-C)
  <= e_{B[C]}(delta T) + a_C(T),
```

where `a_C(T)` counts attachment edges whose C endpoint lies in `T`.
Dropping the nonnegative cross-M term gives

```text
e_{M_C}(delta T) <= e_{B[C]}(delta T) + a_C(T).         (B0)
```

Now take any cut `S` of `H_C`.  If `r` is outside `S`, put `T=S cap C`.
Every private spoke whose C endpoint lies in `T` has endpoints on opposite
sides of `S`, so at least one edge of that spoke crosses.  Summing over
spokes, the H-cut has at least
`e_{B[C]}(delta T)+a_C(T)` B-edges.  Equation `(B0)` proves S2.  If `r` is
inside `S`, apply the same argument to the complementary cut.  This proves
S2 for every cut of `H_C` with no pinned-vertex assumption.

## Metric and triangle audit

The only new way for a path to leave and re-enter `C` goes through `r` and
uses two complete spokes, so it has length at least `2K=Delta`.  Every
within-C M-distance is at most `Delta`; hence no new route shortens one and

```text
d_{H_C}(u,v)=d_{B[C]}(u,v).
```

Deleting vertices and edges cannot make the within-C distance smaller than
the ambient B-distance, yielding the second comparison.  In particular all
M_C distances in `H_C` remain even and at least four.  A triangle with one
M-edge would force B-distance at most two; a triangle with two or three
M-edges is already excluded by triangle-freeness of the original union,
since no new vertex is M-incident.  Thus `H_C union M_C` is triangle-free.

## Exact reproduction

`boundary_completion.py` constructs the graph literally and checks
bipartiteness, simplicity, every completion cut, triangle-freeness, and all
three distance lists.  `test_boundary_completion.py` first applies it to an
exact same-side two-edge component, appends a rooted tail so the completion
is strict, and reproduces

```text
q=7, a=2, K=2, N_C=10<14,
ambient distances = component distances = completion distances = (4,4),
minimum S2 slack = 0.
```

It separately checks a mixed-attachment-side component, for which the four
spokes have lengths `(2,2,3,3)`, `N_C=13`, both M-distances remain four,
and the minimum S2 slack is zero.  Both tests pass using only
integer/Boolean arithmetic.

## Scope and summation frontier

The construction solves a component whenever its completion is both
strictly smaller and its explicit square `N_C^2` fits the remaining RL
budget.  It does not by itself provide a uniform summation: for large `a` or
`Delta`, the term `a(K-1)` can be too expensive.  No same-order Gamma bound
or unproved contraction is used.
