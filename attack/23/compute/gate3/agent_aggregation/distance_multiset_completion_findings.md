# The distance-multiset odd-cycle completion

Status: **proved strict-induction reduction; not full BF-RL and not yet a
Lean graph construction**.

For every even distance `D>=4`, let `m_D` be its multiplicity among the
internal demands and put `q_D=ceil(sqrt(m_D))`.  Take the standard valid
balanced odd-cycle blow-up block `C_{D+1}[q_D]`.  Its standard maximum cut
has `q_D^2` monochromatic edges, all at supply distance `D`.  Retain any
`m_D` of them; deleting monochromatic edges preserves S2 and
triangle-freeness.

Identify one supply-only vertex (in cluster one) across all nonempty
distance blocks.  S2 composes across this articulation because no demand
crosses between blocks.  A simple path between two vertices of one block
cannot leave and re-enter through the sole articulation, so internal
distances are unchanged.  Triangles likewise remain within one block.

The resulting valid instance has the same demand-distance multiset and
exact order

```text
N_multi = 1 + sum_D ((D+1) ceil(sqrt(m_D)) - 1).        (M1)
```

Therefore its Gamma mass is exactly the original `Gamma_int`.  In the
strict RL residual, if

```text
N_multi^2 <= rlBudget(s,d),                             (M2)
```

then `N_multi<n`; strict Gamma induction applies and proves RL.  No original
demand incidence, same-order Gamma call, or unproved routing is used.

The completion is exactly self-tight on both mandatory equality ends:

- one demand of distance `D=n-1`: `N_multi=D+1=n`;
- `q^2` demands of distance four: `N_multi=5q`, the order of `C5[q]`.

For the mixed `(4,6)` series fixture, the articulation identification gives
order `1+(5-1)+(7-1)=11` (stronger than the private order 12).

The exact deterministic BF residual audit currently reports `154/154`
closures by `(M2)` on its 3,000-sample corpus.  This observation is not a
proof dependency.  The remaining quantified problem is to derive `(M2)`
from RFC and the strict residual inequalities, or isolate its exact
complement.

`test_distance_multiset_completion.py` literally constructs the blocks and
their 1-sum, then checks every cut, all distances, triangle-freeness, and the
exact order on long-thin, short-fat, mixed, and nonsquare-multiplicity
fixtures.
