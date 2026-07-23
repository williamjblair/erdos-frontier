# G-B joint frontier: complete corridor-bridge elimination

Status: **PROVED proper enlargement of the banked series slice, plus the
full equality and one-defect boundaries.** This is not a proof of all RL*. It proves RL for
every residual instance having a bridge on a selected root-stub geodesic,
proves the fully nonbridge `d=2s` and `d=2s-1` slices, and reduces the exact
open core to a fully bridge-free corridor with `s >= 5` and `d <= 2s-2`.

## 1. Statement

Let `R=(B,M,w,x0)` be a valid one-stub rooted instance in the strict RL*
residual

```text
n >= 14,  2 <= s,  2*s*p(d) < (d+1)^2,  |M| >= 2,
d = dist_B(w,x0),  s = n-1-d.
```

Fix a `w`-`x0` geodesic `P=(u_0,...,u_d)`. Under the strict Gamma induction
hypothesis, **if any edge of `P` is a bridge of `B`, then `R` satisfies RL**.
Consequently, a minimal residual counterexample may be assumed to satisfy

```text
forall i < d, not IsBridge_B(u_i u_{i+1}),
5 <= s,
d <= 2*s.
```

The equality case in the last display now satisfies RL by
`totalCost_le_rlBudget_of_doubleSlack_allNonbridge_sameSide`. Thus a
remaining counterexample first has `d < 2*s`.  The follow-on theorem
`totalCost_le_rlBudget_of_oneDefect_allNonbridge_sameSide` closes the whole
next row `d=2*s-1`, so the live inequality is `d <= 2*s-2`.

The only remaining quantified lemma is therefore:

> **BF-RL.** Every valid one-stub rooted instance satisfying the displayed
> residual assumptions and admitting a root-stub geodesic all of whose edges
> are nonbridges, with `d <= 2*s-2`, satisfies
> `Gamma_int <= s*(2*d+2+s)+2*s*p(d)`.

BF-RL is a strict graph class, not a renamed unrestricted RL statement.

Within BF-RL, the complete two-demand subregion `2d<s` is now closed by
`totalCost_le_rlBudget_of_twoDemands_twoLength_lt_slack`.  Rooted G-A gives
`2Dmax<=2s+d`, while applying G-A to the two internal geodesics gives
`Dmin+2Dmax<=2(s+d)`; a kernel-checked convex endpoint argument pays both
squares.  This avoids the false raw sum estimate.  Positive even root
distance supplies partner distance two; the same endpoint calculation then
closes `2d<=s` and all four rows `2d-3<=s<=2d`.  Together with the
independent distance-four theorem, the exact remaining two-demand slice has
both distances at least six and either odd `d` with `s<=2d`, or even `d`
with `s<=2d-4`.

## 2. Interior bridge

Let `u_k u_{k+1}` be a bridge with `1 <= k` and `k+1 < d`. Its deletion
gives root and stub components of orders `n1,n2` and positive local distances
`d1=k`, `d2=d-k-1`. The bridge cut lemma gives no M-edge between the two
components. RFC restricts to a valid one-stub block on each side, Gamma and
slack split, and the banked series budget is superadditive.

The exact induction-size gate is

```text
p(d1) < n2  and  p(d2) < n1.                         (G)
```

Indeed the two minimal composites have orders `n1+p(d1)` and `n2+p(d2)`;
both are strictly below `n1+n2` exactly under (G). The Lean theorems
`minimalComposite_sizes_lt_series_of_partner_lt` and
`minimalComposite_sizes_lt_series_iff` retain this exact gate.

Suppose (G) fails and neither component has order two. Since a positive
geodesic fits in each component, `n1,n2 >= 3`. Also `p <= 3`. A failure of
(G) therefore forces one component to have order three and the partner
distance on the other side to equal three. Since `p(t)=3` iff `t=1`, the
global distance is at most four. But `n>=14` then gives `s>=9`; direct
evaluation at `d=3,4` contradicts
`2*s*p(d)<(d+1)^2`. This is
`residual_series_gate_or_endpoint_pair` in Lean.

It remains that one bridge component has order two. Its positive local
distance is one. No legal M-edge lies inside a two-vertex component, and the
bridge lemma excludes an M-edge leaving it. Hence the outer endpoint `w` or
`x0` is an M-free B-leaf. Root move or stub retraction deletes that leaf,
preserves Gamma, produces a smaller valid rooted instance, and does not
increase the budget. The last arithmetic assertion is `rlBudget_pred_le`.

Thus every interior bridge is reduced, including every former side-of-order
two or three exception.

## 3. Endpoint bridge

Consider the first corridor edge `w u_1`; the last edge is symmetric. Let
`A` be its component containing `w`, of order `a`, and let `C` contain the
stub. Again no M-edge crosses the bridge.

If `a <= 3`, then `diam(B[A]) <= a-1 <= 2`, so `A` contains no legal M-edge.
Delete `A` and move the root to `u_1`. Restricting RFC to `C` proves the new
rooted instance valid. Its parameters are

```text
dC = d-1,  sC = s-(a-1),  GammaC = Gamma.
```

Here `a-1 <= s` because `C` contains the `d` vertices
`u_1,...,u_d`. Monotonicity in slack followed by root move gives

```text
F(s-(a-1),d-1) <= F(s,d),
```

where `F=rlBudget`; this is `rlBudget_endpointBlock_retraction_le`.

If `a >= 4`, restriction gives an ordinary valid instance on `A`, so strict
Gamma induction gives `Gamma_A <= a^2`. The rooted block `C` has minimal
composite order `|C|+p(d-1) < |C|+a=n`, because `p <= 3 < a`; hence the
already-proved minimal-composite equivalence gives RL on `C`. Exact expansion
then gives

```text
Gamma_A + F(sC,d-1) <= a^2 + F(sC,d-1)
                      <= F(sC+a-1,d).
```

The second inequality is
`gammaBlock_endpointBridge_le_rlBudget`. Thus endpoint bridges reduce for
every component order. The exhaustive order dispatch itself is kernel checked
as `endpointBlock_small_or_partner_lt`.

## 4. Full nonbridge consequence

Assume every edge of `P` is a nonbridge. For each corridor index `i`, the
banked canonical cut theorem supplies an off-corridor component whose
attachment interval covers `i`. A component `C` of order `q_C` has interval
span at most `q_C+1`. The canonical components partition the `s` vertices
outside `P`, and each has positive order. Therefore

```text
d <= sum_C (q_C+1)
  =  s + number_of_components
  <= 2*s.
```

This entire graph-level count is kernel checked as
`IsGeodesic.length_le_twice_slack_of_all_nonbridge`; it does not assume that
the whole graph is 2-connected. Finally `n=d+1+s>=14` and `d<=2s` imply
`s>=5`, kernel checked as
`IsGeodesic.slack_at_least_five_of_large_all_nonbridge_corridor`.

## 5. Exact frontier change

The previous bank closed only interior bridges with both sides of order at
least four. The present proof closes:

1. all interior side-of-order-three cases through the exact size gate;
2. all interior side-of-order-two cases by M-free endpoint retraction;
3. both endpoint corridor bridges, for every endpoint-component order; and
4. all residual rows `s=2,3,4` as an immediate structural consequence.

What remains is the genuine simultaneous-distance aggregation BF-RL above.
No volume packing, per-vertex load, summed SE1/SE2, or multicommodity
routability statement is used.

## 6. Exact weighted-cut dual interface

One further non-closing interface is banked for BF-RL. For every integer
potential `f:V->Nat`, summing RFC over the threshold cuts `{v:k<f(v)}` gives

```text
sum_{uv in M} |f(u)-f(v)| + |f(w)-f(x0)|
  <= sum_{ab in B} |f(a)-f(b)|.                         (C)
```

The layer-cake identity and (C) are kernel checked as
`sum_thresholdSeparation_eq_dist` and
`rootedCutCondition_natPotential_of_allCuts` (with the threshold-family core
`rootedCutCondition_natPotential`). The original root-excluding RFC form is
connected kernel-side by `rootedCutCondition_natPotential_of_rootCuts`.
This is a genuine cut-dual reformulation,
but it does not itself supply a potential whose left side majorizes the
quadratic Gamma objective at the required right-side cost. That construction
is part of BF-RL and is not claimed.

The complement step is exact: cut edge counts and terminal separation are
unchanged.

The landing condition is also kernel checked. If `|M|>=2`, a bounded
potential `f` and reserve `lambda` suffice when

```text
(D_uv+1)^2 + lambda <= |f(u)-f(v)|       for every uv in M,
sum_B |Delta f| <= |f(w)-f(x0)| + F(s,d) + 2*lambda.
```

Coarea then pays one `lambda` per M-edge and the two guaranteed edges absorb
the `2*lambda` allowance. This is
`rootedCutCondition_totalCost_le_of_potentialCertificate`. The missing BF-RL
work is the uniform construction of such a potential, not the certificate
algebra.

The same landing condition is kernel checked for a finite family of bounded
potentials.  In that form the separation and supply variation are summed over
the family before the reserve argument is applied.  This is
`rootedCutCondition_totalCost_le_of_potentialFamilyCertificate`; in
particular, it covers finite integral weighted-cut metrics and laminar trees,
which need not be the threshold chain of one potential.  The theorem asserts
only that explicitly supplied family data certify the RL budget.  Existence
of a family meeting those inequalities in every BF-RL instance remains the
single open construction and is not claimed.

For auditing a proposed dual without first encoding its cuts as potentials,
`rootedCutCondition_totalCost_le_of_weightedCutCertificate` exposes the same
criterion directly: a finite family of Boolean cuts, one natural weight per
cut, per-demand weighted separation, and the single weighted supply budget.
The conversion of a weighted cut to a two-valued potential is exact, including
weight zero.

Rational cut weights and a rational reserve are covered without a trusted
floating-point step.  After clearing their common denominator by a positive
natural `scale`, the integral costs and budget are multiplied by that same
scale; kernel cancellation returns the unscaled conclusion. This is
`rootedCutCondition_totalCost_le_of_scaledWeightedCutCertificate`.

## 7. Audited equality-boundary arithmetic

Equality in the proved corridor count suggests a separate, narrower route at
`d=2s`: singleton span-two blocks separated by capacity-two articulations.
The finite-set equality step is proved as
`full_coverage_eq_twice_mass_forces_unit_intervals`: full coverage, positive
component sizes summing to `s`, and interval cardinalities at most size plus
one force union cardinality `2s`, pairwise-disjoint intervals, every component
size one, and every interval cardinality two.  The converse-to-union-bound
step is independently exposed as
`pairwiseDisjoint_of_card_biUnion_eq_sum_card`.

The equality statement is also instantiated on the actual graph objects.
If every edge of a geodesic `P` is a nonbridge and
`P.length=2*slack(P)`, then
`IsGeodesic.doubleSlack_allNonbridge_rigidity` proves that every canonical
component of `B-V(P)` is a singleton and that its actual attachment interval
has two edges, with the intervals pairwise disjoint.  The generic interval
lemma `pairwise_twoIntervals_tile_even` then proves these are exactly the
tiles `[2k,2k+2)`; this conclusion is included in the graph-level theorem.

The arithmetic end of that route is exact.  If every demand is assigned a
positive natural resource `r_i`, the resources pack as

```text
sum_i r_i <= s-1,                 D_i <= 2*r_i+2,
```

then for `s>=5`

```text
sum_i (D_i+1)^2 <= F(s,2s).
```

This is `totalCost_le_doubleSlackBudget_of_resourcePacking`.  Its proof uses
`sum r_i^2 <= (sum r_i)^2` and keeps the deliberately loose but sufficient
bound `4R^2+21R <= 5s^2+6s`.

The RFC-facing arithmetic has also been isolated.  With `s-1` articulation
cuts, at most one internal demand crossing each cut, legal distances at least
four, and

```text
D_i <= 2*(number of articulation cuts crossed by i)+2,
```

`totalCost_le_doubleSlackBudget_of_articulationCuts` derives the full RL
budget.

The follow-on equality-boundary module now supplies the formerly missing
graph step.  It constructs a canonical block projection of every graph
vertex onto the singleton even-tile chain.  For each of the `s-1` internal
block boundaries, the associated left-region cut has graph capacity at most
two and separates the root from the stub.  RFC therefore permits at most one
internal demand across that cut.  If a demand crosses `r_i` block cuts, its
endpoints link to their block anchors in at most one step each, yielding

```text
D_i <= 2*r_i+2.
```

At the truncated terminal block the first path estimate is one unit weaker;
same-side bipartite parity removes that unit.  The arbitrary finite demand
index type preserves multiplicity throughout.  The root-excluding RFC is
converted to the symmetric cut form by exact complement identities.

The kernel headline
`totalCost_le_rlBudget_of_doubleSlack_allNonbridge_sameSide` therefore proves
RL unconditionally throughout the fully nonbridge `d=2s`, `s>=5` slice.  Its
hostile dependency audit is
`agent_d2s/equality_boundary_audit.md`.  Combining it with the earlier
`d<=2s` reduction leaves the strict frontier `d<2s`.
