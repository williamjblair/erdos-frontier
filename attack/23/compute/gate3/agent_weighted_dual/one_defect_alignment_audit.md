# Hostile audit: the all-nonbridge `d = 2s-1` row

Verdict: **PASS for the exact stated row.**  The kernel headline is

```text
Erdos23GapGBOneDefectAlignment.
  totalCost_le_rlBudget_of_oneDefect_allNonbridge_sameSide
```

It proves the RL budget for a connected bipartite rooted instance whose
root-stub geodesic has length `2 * slack - 1`, every corridor edge is a
nonbridge, RFC holds on every root-excluding cut, `slack >= 5`, and every
internal demand is same-side and has graph distance at least four.  It does
not claim the remaining rows `d <= 2s-2`, nor does it remove the previously
banked bridge reductions.

## Dependency tree and per-node verdict

1. **Exact interval deficit trichotomy — PASS.**
   `canonical_oneDefect_trichotomy` applies to the finite family of all
   off-corridor connected components.  Since their positive masses sum to
   `s`, their spans are at most mass plus one, and their attachment intervals
   cover all `2s-1` corridor edges, exactly one of mass, span, or overlap
   defect is one.

2. **Span defect elimination — PASS.**
   `canonical_spanDefect_case_false` shows that a span-one singleton would
   attach to both ends of a corridor edge, making a triangle in the Boolean
   coloring.  Thus only the mass and overlap cases survive.

3. **Mass geometry — PASS.**
   `componentShapes_of_massDefect` proves that there is one two-vertex
   component with a saturated three-edge interval and every other component
   is a saturated singleton two-edge interval.  Zero overlap makes these
   intervals disjoint.  `massIntervalProfile` proves that their strict
   interiors form exactly `s` doubled BFS levels, every level gap is active,
   and exactly one gap has both endpoint levels doubled.

4. **Overlap geometry — PASS.**
   `componentShapes_of_overlapDefect` proves that all components are
   saturated singletons with two-edge intervals.  Their total interval
   multiplicity exceeds their union by one.  `overlapIntervalProfile` proves
   that the interval midpoints are distinct, form exactly `s` doubled BFS
   levels, activate every gap, and contain exactly one adjacent pair.

5. **Component vertices equal the claimed BFS levels — PASS.**
   A singleton spanning `[l,l+2)` is forced to rooted level `l+1` and is
   adjacent to both extreme corridor vertices.  A two-vertex component
   spanning `[l,l+3)` contains its internal edge; its left and right extreme
   vertices are forced to levels `l+1,l+2`.  The proofs use only graph
   connectedness, geodesicity, bipartite coloring, and exact triangle
   inequalities.  Summing component masses and comparing image cardinalities
   proves that the off-corridor rooted-level map is injective.

6. **Local one-high routing — PASS.**
   `localOneHighGeometry_of_componentShapes` proves four quantified facts.
   For every ordinary gap, every vertex on one endpoint level is adjacent to
   every vertex on the other.  At the unique high gap every vertex has a
   neighbor across in both directions.  Vertices on a common BFS level have
   graph distance at most two.  The unique span-three component, if present,
   is forced to occupy the high gap; no informal alignment assumption remains.

7. **Demand alignment — PASS.**
   Same-side endpoints have even BFS-level difference.  Legality rules out a
   common level.  The local routing gives a path whose length is their level
   difference, while the BFS triangle inequality gives the reverse bound.
   Hence every demand distance is exactly its BFS-level span.

8. **Binary layer counts — PASS.**
   `levelLayer_card_eq_one_add_indicator` gives literal layer sizes
   `1 + 1_E(k)`.  `indicatorProfile_counts` proves with finite exact sums that
   there are `s` extras, every extra is zero or one, and the sum of adjacent
   extra products is exactly one.  Thus the high-gap budget is `1+1 <= s`.

9. **RFC aggregation and RL landing — PASS.**
   `totalCost_le_rlBudget_of_oneHighBinaryLayerChain` applies the threshold
   cuts.  The automatic binary-layer theorem reserves one unit for the stub,
   aggregates the remaining cut capacities, and proves

   ```text
   sum_i (dist(m1_i,m2_i)+1)^2 <= rlBudget(s,2s-1).
   ```

   Every hypothesis is discharged in the headline theorem.  No theorem of
   RL-equivalent strength is left as an assumption.

## Exact exhaustive reproduction

Run:

```text
python3 compute23/gate3/agent_weighted_dual/one_defect_geometry_check.py
```

The checker uses only integer graph arithmetic.  For every `2 <= s <= 16`
it enumerates every position of the length-three mass block, all four allowed
bipartite attachment choices for that block, and every overlap interval
family.  The overlap generator uses the forced normal form: starts advance by
two, make their unique one-step phase switch at one of `s-1` positions, then
advance by two again.  This is the constructive form of the kernel interval
profile, not a sampled search.  The checker verifies the cover and defect
identities for every generated family.  It also checks geodesicity,
bipartiteness, every corridor edge being a
nonbridge, the exact right-boundary cut capacities, and every same-side pair
at distance at least four.  The exhaustive totals are:

```text
PASS {'mass': 480, 'overlap': 120, 'eligible': 149800}
first_unaligned None
```

The mass case has `s-1` capacity-two right-boundary cuts.  In the overlap
case exactly one right-boundary cut has capacity three; omitting it leaves
`s-1` capacity-two cuts.  The Lean proof uses the equivalent BFS-layer
certificate, not an unformalized appeal to these cuts.

## Falsification record

- **Unaligned 14-vertex fixture:** the previously recorded general binary
  BFS fixture has a legal demand of distance four and level span two.  It is
  not a counterexample here: its off-corridor component intervals do not have
  the mass/overlap one-defect profile forced by `d=2s-1`.
- **Balanced odd-cycle blow-ups and long odd cycles:** their tight `d=1`
  instances are outside the residual `s>=5`, `d=2s-1` row.  No equality from
  those families is imported.
- **Forced hub (`n=8`):** no per-vertex load bound is asserted.
- **Path-packing witness (`n=12`):** no volume or unit-congestion inequality
  is asserted.  Aggregation is by literal BFS threshold-cut capacity.
- **Boundary high gap:** component intervals are strict interiors of
  subsets of `range(P.length)`.  Therefore the high pair lies at levels
  `high,high+1 < P.length`; the routing theorem does not silently index past
  the corridor endpoint.
- **Small slack:** the geometry checker includes `s=2,3,4`; the headline
  theorem deliberately retains the residual assumption `s>=5` needed by
  the surrounding RL reduction.

## Kernel and source gate

```text
lake env lean ErdosProblems/Erdos23GapGBOneDefectAlignment.lean
scripts/check_axioms.sh
```

The direct source compilation reports exactly
`[propext, Classical.choice, Quot.sound]` for the headline theorem.  The
module contains no `sorry`, new `axiom`, `native_decide`, floating-point
claim, or private theorem-strength hypothesis.

## Exact remaining frontier

After this theorem, the fully nonbridge near-boundary frontier begins at the
single quantified row

```text
d <= 2 * s - 2.
```

The current `Erdos23GapGBTwoDefect` module classifies the five aggregate
`d=2s-2` interval shapes, but their unconditional graph-to-demand alignment
and RL aggregation are not supplied by this theorem.
