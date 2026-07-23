# Hostile audit: Erdős 23 `d = 2s` equality boundary

Verdict: **PASS for the unconditional bridge-free `d = 2s` slice of BF-RL.**
This does not prove BF-RL for `d < 2s`, RL* in full, or Erdős #23.

## Exact theorem

`ErdosProblems/Erdos23GapGBEqualityBoundary.lean` proves
`totalCost_le_rlBudget_of_doubleSlack_allNonbridge_sameSide`.

Let `G` be a finite connected graph with a Boolean proper coloring, let `P`
be a root-to-stub geodesic, and let the internal demands be indexed by an
arbitrary finite type `I`. Assume:

```text
length(P) = 2 * slack(P),
every edge of P is a nonbridge,
5 <= slack(P),
dist_G(m1(i),m2(i)) >= 4 for every i,
color(m1(i)) = color(m2(i)) for every i,
and root-form RFC for every finite T avoiding the root.
```

Then

```text
sum_i (dist_G(m1(i),m2(i)) + 1)^2
  <= rlBudget(slack(P), 2*slack(P)).
```

The finite index type permits repeated demands, so RFC multiplicity is not
silently discarded.

## Dependency tree

1. **Threshold arithmetic — PASS.**
   - The `s-1` internal articulation thresholds record block-coordinate
     distance exactly unless one endpoint is the terminal block, in which
     case they lose exactly at most one.
   - Kernel:
     `blockCoordinate_boundarySeparation_eq_dist_of_lt` and
     `blockCoordinate_dist_le_boundarySeparation_add_one`.

2. **Every component is an even tile — PASS.**
   - The banked rigidity theorem supplies every even tile and pairwise
     disjoint two-edge intervals. A nonempty interval for an arbitrary
     component meets one supplied tile; pairwise disjointness forces equality.
   - Kernel:
     `IsGeodesic.every_offCorridorComponent_is_even_tile`.

3. **Tile endpoints are actual attachments — PASS.**
   - Equality with `[2k,2k+2)` forces the minimum attachment to be `2k` and
     the maximum attachment to be `2k+2`; both extrema belong to the actual
     attachment set. Singleton component cardinality makes their witnesses
     the same off-corridor vertex.
   - Kernel: `attachment_extrema_of_interval_eq_two` and
     `IsGeodesic.exists_tileVertex_adj_endpoints`.

4. **Canonical block projection — PASS.**
   - A corridor vertex at coordinate `j` projects to block `j/2` at distance
     at most one. An off-corridor vertex projects to the left articulation of
     its unique tile, also at distance one. Membership in every internal
     boundary cut is exactly `block < k+1`.
   - The only vertex in terminal block `s` is the terminal articulation.
   - Kernel: `IsGeodesic.exists_boundaryProjection`.

5. **Per-demand distance comparison — PASS.**
   - Two projected anchors have distance twice their block-coordinate
     distance. If neither endpoint is terminal, the cut count is exact and
     the two endpoint links give `D <= 2r+2`.
   - If one endpoint is terminal, threshold truncation initially gives the
     odd upper bound `2r+3`; same-side bipartite parity removes the last unit.
   - Kernel: `IsGeodesic.dist_even_anchors`,
     `Coloring.even_dist_of_eq`, and
     `IsGeodesic.dist_le_twice_sum_boundaryCuts_add_two`.

6. **Cut capacity — PASS.**
   - At the cut immediately before articulation `P[2k+2]`, every oriented
     crossing graph edge is either the corridor edge
     `P[2k+1]-P[2k+2]` or the unique tile-vertex edge into `P[2k+2]`.
   - This classification covers all four support/off-corridor endpoint cases.
     Adjacent off-corridor vertices lie in one canonical component and hence
     cannot cross; a path-to-off-corridor crossing in the opposite orientation
     contradicts the definition of the left region.
   - Kernel: `IsGeodesic.exists_boundaryCrossing_classifier` and
     `IsGeodesic.cutSize_boundaryLeftCut_le_two`.

7. **RFC capacity one — PASS.**
   - Every internal boundary cut separates the root and stub, so terminal
     load is one. Graph capacity is at most two; RFC therefore leaves capacity
     at most one for all internal demands combined.
   - The source proves complement invariance of demand separation and graph
     cut size and converts the literal root-excluding RFC to the symmetric
     all-cuts form.
   - Kernel:
     `IsGeodesic.separationDemand_boundaryLeftCut_terminals_eq_one`,
     `separationDemand_univ_sdiff`, `cutSize_univ_sdiff`, and
     `symmetricRootedCutCondition_of_rootForm`.

8. **Quadratic aggregation — PASS.**
   - The `s-1` cut resources have capacity at most one, every legal demand
     crosses at least one by `D>=4` and `D<=2r+2`, and the banked exact
     resource arithmetic gives the RL budget.
   - Kernel: existing
     `totalCost_le_doubleSlackBudget_of_articulationCuts`, instantiated by
     `totalCost_le_rlBudget_of_doubleSlack_allNonbridge_rootForm` and its
     same-side corollary.

## Boundary and falsification checks

- **`s=5`:** all natural subtractions are exact (`Fin (s-1)` has four cuts);
  the arithmetic theorem is stated with the non-strict boundary `5 <= s`.
- **First and last internal cuts:** cuts are indexed by `k=0,...,s-2`, hence
  occur immediately before coordinates `2,...,2s-2`. The missing terminal
  threshold is handled explicitly in the distance proof.
- **Terminal demand endpoint:** not assumed absent. The parity step is exactly
  what closes this case.
- **Same-block endpoints:** zero crossed cuts imply `D<=2`; legality `D>=4`
  therefore excludes such a demand automatically.
- **Repeated demands:** allowed by the arbitrary finite index type and charged
  with multiplicity in every RFC sum.
- **Mixed distances:** no constant-distance assumption occurs.
- **Both equality-family ends:** the theorem is restricted to `d=2s` and
  `s>=5`; no claim is made about the `d=1` tight family. Within the stated
  boundary it proves the exact RL inequality, not a stronger false volume or
  load bound.
- **Forced hub and path-packing witnesses:** no vertex-load, volume-packing,
  shortest-path routing, or multicommodity-routability assertion is used.
- **Strict residual boundary:** the result removes the equality row `d=2s`
  only. Combined with the already proved `d<=2s`, the remaining BF-RL regime
  is `d<2s`.

## Exact arithmetic and kernel gate

All arithmetic is natural-number arithmetic discharged in Lean. There is no
floating point, enumeration dependency, `native_decide`, `sorry`, private
lemma, or new axiom.

```text
lake env lean ErdosProblems/Erdos23GapGBEqualityBoundary.lean
```

prints only `[propext, Classical.choice, Quot.sound]` or subsets for every
headline theorem, including
`totalCost_le_rlBudget_of_doubleSlack_allNonbridge_sameSide`.

## Remaining quantified lemma after this slice

For every valid one-stub rooted instance in the BF-RL residual with

```text
n >= 14, |M| >= 2, 5 <= s, d < 2s,
2*s*p(d) < (d+1)^2,
and an all-nonbridge root-stub geodesic,
```

prove

```text
sum_{uv in M} (dist_B(u,v)+1)^2
  <= s*(2*d+2+s) + 2*s*p(d).
```

No claim beyond this strict frontier reduction is made.
