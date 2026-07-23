# Hostile audit: one-defect finite interval profiles

Verdict: **PASS for both exact finite-set profile theorems.**  These results
translate the two surviving abstract interval geometries into a zero-one
level profile.  They contain no graph-distance or RFC claim.

## Mass profile

Assume pairwise-disjoint integer intervals tile `[0,2s-1)`, exactly one has
length three, and all others have length two.  The strict interval interiors
then:

- have total cardinality `s`;
- contain at least one endpoint of every corridor gap; and
- contain both endpoints of exactly one gap.

The proof uses exact union cardinalities, the unique length-three block, and
pairwise disjointness.  The uniqueness step proves that adjacent interior
points must belong to the same interval; a length-two interval cannot contain
them both.

Kernel theorem: `massIntervalProfile`.

## Overlap profile

Assume `s` length-two integer intervals cover `[0,2s-1)`.  Their midpoint
set `E` covers every corridor gap.  The proof forms `E union pred(E)`:

- every midpoint is positive and below `2s-1`, so predecessor is injective
  on `E`;
- the union is exactly the corridor edge range;
- image cardinality gives `|E|=s`; and
- the exact union/intersection identity gives `|E intersect pred(E)|=1`.

Consequently interval starts are injective and exactly one pair of midpoint
levels is adjacent.

Kernel theorem: `overlapIntervalProfile`.

## Scope checks

- Intervals are literal `Finset.Ico` sets over naturals; “tile” and “one
  overlap” are not pictorial assumptions.
- Terminal and initial coordinates are included in the range equalities.
- The overlap theorem proves start injectivity rather than assuming it.
- No bounded computation, ordering choice, floating point, private lemma,
  `native_decide`, or graph-level uniformity enters either result.
- The graph application must still prove that canonical off-corridor
  vertices occupy these interior/midpoint BFS levels and that legal demands
  are level aligned.

## Kernel gate

```text
lake env lean ErdosProblems/Erdos23GapGBOneDefectIntervals.lean
```

Both theorems print only `[propext, Classical.choice, Quot.sound]`.
