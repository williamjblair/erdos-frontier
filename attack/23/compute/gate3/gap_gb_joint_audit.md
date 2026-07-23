# Hostile audit: G-B corridor-bridge elimination

Verdict: **PASS for the quantified bridge elimination and bridge-free
reduction. Full RL* remains unproved.**

## Dependency tree

1. **Partner-distance identities — PASS.**
   - Exact claims: `1 <= p(d) <= 3`; `p(d)=3` iff `d=1`; predecessor and
     successor changes are at most one in the directions used.
   - Kernel: `partnerDistance_pos`, `partnerDistance_le_three`,
     `partnerDistance_eq_three_iff`, `rlBudget_pred_le`.

2. **Exact interior induction gate — PASS.**
   - Claim: the two minimal composites are strict subinstances iff
     `p(d1)<n2` and `p(d2)<n1`.
   - Kernel: `minimalComposite_sizes_lt_series_of_partner_lt`,
     `minimalComposite_sizes_lt_series_iff`.
   - No non-strict or uniform `n_i>=4` substitution remains.

3. **Residual gate dispatch — PASS.**
   - Quantified claim: under `n>=14`, exact size/distance splitting, and
     `2*s*p(d)<(d+1)^2`, gate failure implies `n1=2` or `n2=2`.
   - Kernel: `residual_series_gate_or_endpoint_pair`.
   - Independent exact reproduction: all admissible tuples with
     `2<=n1,n2<40` in `test_gap_gb_joint_verify.py`.

4. **Two-vertex interior side — PASS.**
   - Positive local distance plus order two makes the outer endpoint a
     leaf. Distance at most one inside the component excludes every legal
     M-edge; the bridge lemma excludes crossing M-edges.
   - Existing paper nodes: M-free root move and stub retraction, Lemmas
     3.2 and 3.3 of `lemma_rl_proof.md`.
   - Budget kernel: `rlBudget_pred_le`.

5. **Small endpoint block — PASS.**
   - For `a<=3`, connectedness gives diameter at most two, so no M-edge can
     satisfy `d_B>=4`. RFC restriction is literal because no M-edge crosses
     the bridge. Exact parameter change is `d-1`, `s-(a-1)`.
   - Budget kernel: `rlBudget_endpointBlock_retraction_le`.

6. **Large endpoint block — PASS.**
   - For `a>=4`, `p(d-1)<=3<a` supplies the strict minimal-composite gate
     for the remaining rooted block. The endpoint block itself is an
     ordinary smaller valid instance and receives the stated `a^2` Gamma
     bound from the induction hypothesis.
   - Budget kernel: `gammaBlock_endpointBridge_le_rlBudget`.
   - Exhaustive small/large order split:
     `endpointBlock_small_or_partner_lt`.

7. **Canonical interval cover — PASS.**
   - Every specified nonbridge corridor edge is covered by a canonical
     off-corridor component interval; span is at most component order plus
     one; component orders sum exactly to `s`; component count is at most
     `s`.
   - Kernel: `IsGeodesic.corridorIndexSet_card_le_twice_slack` and its
     already-verified dependencies in `Erdos23GapGA*.lean`.

8. **Full bridge-free parameter reduction — PASS.**
   - Exact claims: all corridor edges nonbridge implies `d<=2s`; with
     `n=d+1+s>=14`, this implies `s>=5`.
   - Kernel: `IsGeodesic.length_le_twice_slack_of_all_nonbridge`,
     `IsGeodesic.slack_at_least_five_of_large_all_nonbridge_corridor`.

9. **Integer-potential coarea interface — PASS, non-closing.**
   - Every threshold invokes exactly one RFC cut; finite sum interchange and
     the exact layer-cake identity give the displayed total-variation bound.
     Thresholds containing the root use the complementary RFC cut, which has
     identical edge counts and terminal separation.
   - Kernel: `sum_thresholdSeparation_eq_dist`,
     `rootedCutCondition_natPotential`, and
     `rootedCutCondition_natPotential_of_allCuts`, with original RFC supplied
     by `rootedCutCondition_natPotential_of_rootCuts`.
   - No potential with target-strength quadratic separation is asserted.
   - The exact sufficient certificate algebra is kernel checked by
     `totalCost_le_of_potentialCertificate` and
     `rootedCutCondition_totalCost_le_of_potentialCertificate`.  The finite
     weighted-cut version is
     `rootedCutCondition_totalCost_le_of_potentialFamilyCertificate`, with
     the direct Boolean-cut surface
     `rootedCutCondition_totalCost_le_of_weightedCutCertificate` and its
     denominator-cleared rational form
     `rootedCutCondition_totalCost_le_of_scaledWeightedCutCertificate`.
     Existence of either required certificate is explicitly not asserted.

10. **`d=2s` equality boundary — PASS, closing this slice.**
    - Equality in the finite interval count forces size-one components and
      pairwise-disjoint two-coordinate intervals; kernel:
      `full_coverage_eq_twice_mass_forces_unit_intervals`.
    - The same conclusion for the actual canonical components and attachment
      intervals of an all-nonbridge geodesic is kernel checked as
      `IsGeodesic.doubleSlack_allNonbridge_rigidity`.
      Its even-tiling node is `pairwise_twoIntervals_tile_even`.
    - Quantified claim: for `s>=5`, positive resources with total at most
      `s-1` and `D_i<=2r_i+2` imply the exact RL budget at `d=2s`.
    - Kernel: `totalCost_le_doubleSlackBudget_of_resourcePacking`.
      The cut-count specialization is
      `totalCost_le_doubleSlackBudget_of_articulationCuts`.
    - The follow-on module `Erdos23GapGBEqualityBoundary.lean` constructs the
      actual `s-1` block cuts, proves their graph capacity is at most two,
      obtains internal-demand capacity at most one from RFC, and proves
      `D_i <= 2r_i+2`, including the terminal-block parity case.
    - Kernel headline:
      `totalCost_le_rlBudget_of_doubleSlack_allNonbridge_sameSide`.
      Thus `d=2s` is excluded from the remaining lemma.

11. **`d=2s-1` one-defect boundary — PASS, closing this slice.**
    - The exact interval-defect identity gives one mass, span, or overlap
      defect; bipartiteness eliminates span.
    - The two surviving cases have a kernel-checked one-high binary BFS
      profile. Canonical component geometry proves ordinary-gap completeness,
      two-sided routing at the unique high gap, same-layer diameter at most
      two, and exact alignment of every legal same-side demand.
    - Kernel headline:
      `Erdos23GapGBOneDefectAlignment.totalCost_le_rlBudget_of_oneDefect_allNonbridge_sameSide`.
      The independent exact checker covers 88 mass geometries, 22 overlap
      geometries, and 6,910 eligible pairs for `5 <= s <= 8`. Thus
      `d=2s-1` is also excluded by the quantified Lean theorem, while the
      finite checker remains falsification support rather than its proof.

12. **Two-demand weighted slices — PASS.**
    - Symmetric RFC for `Fin 2` demands implies the internal two-demand cut
      condition.  The two orientations of G-A give
      `Dmin+2Dmax<=2(s+d)`; rooted G-A gives `2Dmax<=2s+d`.
    - Exact convex endpoint arithmetic proves the RL cost whenever `2d<s`.
      Partner distance two additionally proves the closed ratio `2d<=s`
      for even `d` and the four rows through `s=2d-3`. Kernel headlines:
      `Erdos23GapGBTwoDemandWeighted.totalCost_le_rlBudget_of_twoDemands_twoLength_lt_slack`.
      `Erdos23GapGBTwoDemandWeighted.totalCost_le_rlBudget_of_twoDemands_even_near_twiceLength`.
    - The arithmetic checkers exhaust 7,377,764 tuples in total, and the
      exact `n=76` GB-2SUM counterexample lies inside the proved ratio.

## Falsification record

- **Both equality-family ends:** no global joint-distance inequality is
  asserted. The long-tail C5 blow-up is explicitly reproduced and violates
  `sum D<=2s`; its tail bridge is handled by series reduction. The tight
  `d=1` equality family lies outside the residual.
- **n=8 forced hub:** reproduced exactly (`load=10>8`). No vertex-load
  statement occurs in the proof.
- **n=12 path packing:** reproduced exactly (`sum(D+1)=20>18` and
  `sum D=16>14`). No volume or unit-congestion statement occurs.
- **Mixed distances:** the rooted `[4,6]` fixture is reproduced exactly;
  no constant-distance hypothesis occurs.
- **Two-demand joint sum:** the exact all-nonbridge strict-residual fixture
  `n=76,d=11,s=64,p=1,(D1,D2)=(38,38)` falsifies
  `D1+D2<=n+p(d)-2` by one while satisfying RL by 2718.  No such linear
  estimate is used or left as an asserted route.
- **Strict boundaries:** the residual predicate uses strict `<`; the gate
  uses strict `<`; two- and three-vertex sides are dispatched separately.
- **Endpoint edges:** treated explicitly in both orientations, not silently
  included in the positive-distance series theorem.
- **Natural subtraction:** `a-1<=s` is quantified from the retained
  geodesic vertices; the Lean budget theorem is valid even before using
  that side condition.

## Exact arithmetic reproduction

`python -m pytest -q compute23/gate3/test_gap_gb_joint_verify.py` checks:

- all mandatory killed fixtures;
- the strict residual boundary;
- exact interior size-gate extension;
- exhaustive bounded residual dispatch;
- a `100 x 98` endpoint-move grid; and
- a `98 x 100 x 99` endpoint-block absorption grid; and
- every threshold pair through height 99 for the layer-cake identity; and
- every positive resource composition with `5<=s<=13` for the `d=2s`
  arithmetic certificate.

All arithmetic is integer arithmetic. No floating point or heuristic result
is a proof dependency; the discovery-only random harness was not banked.

## Kernel gate

`lake env lean ErdosProblems/Erdos23GapGBJoint.lean` reports only
`[propext, Classical.choice, Quot.sound]` or subsets for every new theorem.
There is no `sorry`, `axiom`, private theorem, or `native_decide`.

## Single remaining quantified lemma

For every valid one-stub rooted instance with

```text
n>=14, |M|>=2, 5<=s, d<=2s-2,
2*s*p(d)<(d+1)^2,
and some w-x0 geodesic P satisfying
  forall i<d, not IsBridge_B(P_i P_{i+1}),
```

prove

```text
sum_{uv in M} (d_B(u,v)+1)^2
  <= s*(2*d+2+s)+2*s*p(d).
```

This below-one-defect statement is the remaining BF-RL. No theorem-strength
replacement for it is claimed.
