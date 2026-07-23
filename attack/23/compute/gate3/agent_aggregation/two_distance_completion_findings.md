# Exact two-distance completions

Status: **proved paper constructions and executable all-cut audits; not full
BF-RL and not Lean graph constructors**.

For distinct even distances `4<=a<b`, take a supply path `P_b` and, over
each consecutive two-edge block of its first `a` edges, add one singleton
detour vertex.  Use demands `(0,a)` and `(0,b)`.  The long demand is paid by
`P_b`; the short demand is paid by the chain of detours.  These two paths
are edge-disjoint, so S2 holds for every cut.  Distances are exactly `a,b`,
and the order is

```text
N_distinct(a,b) = b+1+a/2.
```

In particular `(4,8)` has order 11 and therefore fits every `n>=14,s>=5`
RL budget by the kernel-checked absolute floor `F>=135`.  `(4,6)` improves
from the articulation multiset order 11 to order 9.

For two equal copies of even distance `D`, use a layered chain with sizes
`1,2,1,2,...,1,2,2` (D edges).  Put both demands from the initial singleton
to the two vertices in the final layer.  The layers contain two
edge-disjoint routes, giving S2, and

```text
N_equal(D) = 3D/2+2.
```

Both constructions are bipartite and triangle-free because every demand
has supply distance at least four; in the distinct case the two other
demand endpoints are even-separated on the path, and in the equal case
they lie in one independent final layer.

These completions close a proper strict-induction subregime whenever their
order-square fits `rlBudget(s,d)`.  They do not close `(6,8)` at the minimum
frontier budget: order 12 gives 144 while the actual cost is 130 and the
minimum budget is 135.  This explicitly marks the remaining rounding gap.
