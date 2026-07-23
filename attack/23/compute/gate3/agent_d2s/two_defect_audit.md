# Hostile audit: Erdős 23 `d = 2s-2` two-defect boundary

Verdict: **PASS for the exact deficit classification, bipartite
eliminations, pointwise overlap classification, two-high-column capacity
arithmetic, RFC charging of a cut-supported exception, and the complete
abstract RL landings for the saturated size-three and pure-span
exceptions.** The graph constructor still has to derive those literal
profile and exception hypotheses from the canonical components. This audit
therefore does not yet claim that the `d=2s-2` BF-RL row is closed.

## Dependency tree

The kernel source is
`ErdosProblems/Erdos23GapGBTwoDefect.lean`.

1. `intervalDefect_identity` from the one-defect module gives
   `massDefect + spanDefect + overlapDefect = 2`.
2. `sum_eq_two_cases` classifies every natural-valued finite sum of two.
3. The mass and span support lemmas refine the six aggregate allocations.
4. `no_singleton_offCorridorComponent_span_one` eliminates every surviving
   occurrence of a singleton span-one component.
5. Finite multiplicity double counting classifies overlap defect two.
6. A pigeonhole argument for literal length-two integer intervals eliminates
   the abstract triple-covered-coordinate branch.
7. `IsGeodesic.canonical_twoDefect_five_shapes` instantiates the result on
   the actual canonical components of an all-nonbridge geodesic.
8. `totalCost_le_rlBudget_of_nearBoundary_adjacentExtras` lands any aligned
   graph profile with total gap weight at most `2s` and adjacent-extra
   interaction at most two in the exact RL budget.
9. `twoHighColumns_fin_profile_bounds` proves that at most two columns of
   height at most three over a baseline of one give `C<=d+4` and
   `Q<=d^2+8`.
10. `rootedCutCondition_atMostOne_cutSupported_exception` proves directly
    from RFC that a residual-unit cut supports at most one exceptional
    internal demand; its singleton corollary is the pendant charging rule.
11. `totalCost_le_rlBudget_of_pureSpan_twoHighColumns` and
    `totalCost_le_rlBudget_of_pureSpan_stubBaselineColumns` land respectively
    the interior and terminal pendant-leaf profiles, including BFS level
    `d+1`.
12. `totalCost_le_rlBudget_of_q3_twoHighColumns` lands a unique saturated
    size-three exception with exact local data `(D,L)=(4,0)` or `(4,2)`.

Every node above is kernel checked with only
`[propext, Classical.choice, Quot.sound]`.

## Exact five-shape classification

Write `q_C=|C|`, `h_C=|I_C|`, and let the three deficits be

```text
M = s - number of components,
S = sum_C (q_C+1-h_C),
O = sum_C h_C - |union_C I_C|.
```

Complete nonbridge coverage and `d=2s-2` give `M+S+O=2`. There are six
aggregate natural triples. Bipartiteness removes `(0,1,1)`, leaving:

1. `(2,0,0)`: either one `(q,h)=(3,4)` component or two `(2,3)`
   components; all other components have `(1,2)`.
2. `(1,1,0)`: the unique span loss lies on the unique size-two component,
   which has `(q,h)=(2,2)`; every other component has `(1,2)`.
3. `(1,0,1)`: one `(2,3)` component, all others `(1,2)`, and one unit of
   interval overlap.
4. `(0,2,0)`: one singleton has span zero and every other component has
   `(1,2)`. The alternative of two span-one singletons is impossible.
5. `(0,0,2)`: every component has `(1,2)` and there are two units of
   interval overlap.

Kernel headlines:

- `massTwo_spanZero_structure`;
- `massOne_spanOne_structure_of_no_unit_span_one`;
- `massOne_spanZero_structure`;
- `pureSpanTwo_structure_of_no_unit_span_one`;
- `massZero_spanZero_structure`;
- `twoDefect_five_shapes_of_no_unit_span_one`;
- `IsGeodesic.canonical_twoDefect_five_shapes`.

## Pointwise overlap audit

`overlapDefect_eq_sum_multiplicityPred` proves the exact identity

```text
O = sum_{j in the corridor} (number of intervals covering j - 1).
```

For `O=1`, exactly one edge is double-covered. For `O=2`, the abstract sum
allows either one triple-covered edge or two double-covered edges. The first
branch is impossible for length-two integer intervals: an interval covering
`j` starts at `j-1` or `j`; three intervals therefore contain two with the
same start, and those two also overlap on the other edge of their common
interval. That supplies a third unit of overlap, a contradiction.

Thus the pure-overlap shape has exactly two distinct double-covered edges,
and the mixed mass-overlap shape has exactly one. Kernel:

- `lengthTwo_triple_forces_second_overlap`;
- `overlapDefect_two_lengthTwo_structure`;
- `canonical_pureOverlap_two_double_coordinates`;
- `canonical_massOverlap_unique_double_coordinate`.

## Capacity landing

At a BFS gap let `x` and `y` be the extra vertices in its adjacent layers.
The complete-layer residual capacity is

```text
c = x + y + xy,
```

and `c <= (x+y)^2`. If

```text
sum_gaps (x+y) <= 2s
and
sum_gaps xy <= 2,
```

then `sum c <= 2s+2`. The arbitrary-capacity layer theorem therefore gives
the exact `d=2s-2` RL budget for every demand family whose distances equal
their BFS-level spans. This is
`totalCost_le_rlBudget_of_nearBoundary_adjacentExtras`.

No step infers level alignment from RFC.

The profile aggregate no longer needs to be reproved separately for each
shape. If a finite set `high` has cardinality at most two and

```text
c_r <= 3 for r in high,
c_r <= 1 otherwise,
```

then kernel arithmetic gives

```text
C = sum_r c_r <= d+4,
Q = sum_{r,q} min(c_r,c_q) <= d^2+8.
```

For the terminal pure-span attachment every corridor column is baseline,
and the sharper theorem gives `C<=d`, `Q<=d^2`.

## Exact unaligned arithmetic landings

Let `L_i` be the number of threshold columns crossed by demand `i`.
`totalCost_le_rlBudget_of_one_addTwo_exception` proves the exact matrix
bound when every row but one is aligned and the exceptional row satisfies
`D_e<=L_e+2`. Its displayed scalar loss is

```text
16 L_e + 34.
```

There is no asymptotic or unquantified uniformity. For an interior pendant
attachment, `L_e<=d-2` and the two-high profile closes the RL budget for
every `s>=5`. For attachment at the stub, `L_e<=d-1` but the sharper
baseline profile closes the budget. Thus the previously recorded level
`d+1` boundary case is not discarded.

The chordless saturated size-three block also permits a central local pair
with `D-L=4`, so the `+2` theorem cannot be used for it. The separate scaled
exception theorem charges its exact cost: every possible exceptional row
has `D=4` and `L=0` or `L=2`, giving a worst scaled correction of 96 and a
total envelope loss of 100. Together with `Q<=d^2+8`, `C<=d+4`, this closes
for every `s>=5`, including `s=5` without finite case evaluation.

## Exact structural constructor/checker

`two_defect_geometry_verify.py` constructs the seven refined interval
types: the two pure-mass partitions, mixed mass/span, mixed mass/overlap,
pure span, a duplicated length-two interval, and two one-edge overlaps. It
enumerates every exceptional position and all bipartite-compatible optional
attachments in size-two and size-three components for `s=4,...,8`.

For every graph it reproduces the three deficits, interval multiplicities,
root-stub geodesic, bipartition, BFS layers, every legal same-side pair, and
the exact adjacent-extra capacity profile. Reproduction:

```text
$ python3 compute23/gate3/agent_d2s/two_defect_geometry_verify.py
geometry_cases = 1505
cases_by_shape =
  mass_q3 320, mass_q2_q2 560, mass_span 50, mass_overlap 440,
  pure_span 55, overlap_duplicate 25, overlap_two 55
legal_pairs = 85145
aligned_pairs = 84570
unaligned_pairs = 535
outside_pairs = 40
fully_aligned_cases = 1200
largest_adjacent_extra = 2
largest_capacity_excess = 2
verdict = PASS
```

The bounded enumeration is falsification support only. The all-`s`
classification and overlap obstruction are the Lean theorems above.

## Explicit unaligned structural types

The exact check found no unaligned legal pair in either pure-mass shape with
two size-two blocks or either pure-overlap interval type. Four structural
families can contain unaligned pairs. Their arithmetic status is now:

1. **Size-three saturated block:** a path vertex and one of the three local
   block vertices can have supply distance four while their root-level span
   is zero or two. The abstract one-exception RL landing is proved; the
   graph constructor must exhibit the residual-unit local cut in the
   chordless case and the unique candidate in the chorded cases.
2. **Mixed mass/span block:** the second vertex of the size-two span-two
   component is a one-edge tip off the doubled chain; pairs from that tip to
   the right tail need not be level aligned. The generic `+2` landing
   applies once the singleton tip cut and `L<=d-2` are instantiated.
3. **Mixed mass/overlap block:** when the unique overlap touches the
   size-two span-three block, one adjacent singleton/block endpoint pair can
   be unaligned. This is local to the overlap macro-block; the generic `+2`
   landing applies once that single simple pair is identified.
4. **Pure-span leaf:** the span-zero singleton is a pendant vertex. Pairs
   from it to either tail need not be level aligned, and attachment at the
   stub gives BFS level `d+1`. Both the interior two-high-column profile and
   terminal baseline profile have separate kernel-clean RL landings.

These are structural families indexed by the exceptional block and local
attachment pattern, not exceptions bounded by `s`.

## Single remaining quantified graph lemma

Let `R=(B,M,w,x0)` be a valid one-stub rooted instance with a proper Boolean
bipartition, at least two internal demands, and an all-nonbridge `w`-to-`x0`
geodesic `P` satisfying

```text
5 <= s,
length(P) = 2s-2,
dist_B(m1(i),m2(i)) >= 4,
and color(m1(i)) = color(m2(i)).
```

Using the five canonical shapes proved above, construct the BFS threshold
columns and prove the following literal local interface.

```text
Either every legal internal demand is level aligned,
or there is a unique exceptional demand e such that:

* in the saturated size-three block, (D_e,L_e)=(4,0) or (4,2);
* in each other unaligned block, D_e<=L_e+2;
* an interior pendant or tip exception has L_e<=d-2;
* a terminal pure-span exception has L_e<=d-1 and every column c_r<=1;
* otherwise there is a set high of at most two columns with
  c_r<=3 on high and c_r<=1 off high.
```

For a pendant or tip, uniqueness must come from its singleton cut and RFC.
For the chordless size-three block it must come from an explicitly exhibited
residual-unit local cut; chorded cases may instead use the unique candidate
pair. Once this interface is proved, the kernel theorems in this module give
the exact RL inequality directly. Bounded enumeration is not admissible as
the proof of this graph constructor lemma.

## Falsification record

- No multicommodity routing, path packing, volume aggregation, or vertex-load
  theorem is asserted.
- Mixed demand distances and repeated endpoint incidence remain allowed.
- The level theorem is conditional on literal per-demand alignment.
- The pure-span terminal attachment at level `d+1` has its own baseline
  profile theorem; it is not silently truncated into the interior case.
- The overlap multiplicity-three branch was challenged and eliminated in
  Lean, not discarded from finite data.
- This module makes no claim about `d<2s-2`, the multi-stub induction, or the
  final connected/2-connected core.

## Kernel gate

```text
lake env lean ErdosProblems/Erdos23GapGBTwoDefect.lean
```

There is no `sorry`, `axiom`, private theorem, floating-point computation,
or `native_decide`.
