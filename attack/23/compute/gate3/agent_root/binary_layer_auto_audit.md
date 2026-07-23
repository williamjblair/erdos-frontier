# Hostile audit: automatic binary-layer profile

Verdict: **PASS for the stated conditional wrapper.**  This result removes
only finite profile bookkeeping from the already audited level-aligned
binary-layer theorem.  It does not prove that an arbitrary rooted instance
has binary layers or that an arbitrary demand is level aligned.

## Dependency tree

1. `binaryActive_add_binaryHigh`: for endpoint extras `a,b` in `{0,1}`,
   the canonical indicators satisfy `active+high=a+b`.
2. `binaryLayerProduct_eq_profile`: the corresponding layer product is
   `(a+1)(b+1)=1+active+2 high`.
3. `sum_adjacentExtras_le_twice_sum`: summing endpoint extras over all
   gaps counts each level at most twice.
4. `sum_binaryProfile_le_twice_sum`: therefore `L+H` is at most twice
   the total number of extra layer vertices.
5. `totalCost_le_rlBudget_of_binaryLayerExtras_levelAligned`: literal
   layer cardinalities, at most `s` extra vertices, the explicit sharp
   high-gap count, RFC, and literal level alignment instantiate
   `Erdos23GapGBBinaryLayers.totalCost_le_rlBudget_of_binaryBfsLayers_levelAligned`.

Every node is a theorem in
`ErdosProblems/Erdos23GapGBBinaryLayerAuto.lean` except the final imported
binary-layer theorem.  There is no computational extrapolation.

## Adversarial scope checks

- The theorem retains `haligned` as an equality for every demand.  The known
  unaligned fixture therefore does not satisfy its hypotheses.
- The theorem retains the exact adjacent-edge level-step hypothesis and the
  literal cardinality of every level through `d`; binary layers are not
  inferred from vertex count alone.
- `extra k <= 1`, `sum extra <= s`, and `sum high + 1 <= s` are separate,
  quantified inputs.  In particular the last inequality is not silently
  inferred from a vague sparsity statement.
- Mixed demand distances, shared endpoints, and arbitrary finite demand
  multiplicity remain allowed.  No path packing or per-vertex load is used,
  so the double-broom and path-packing falsifiers do not attack a premise.
- The wrapper uses the same exact RL budget as the imported theorem and adds
  no asymptotic or floating-point bound.

## Kernel gate

```text
lake env lean ErdosProblems/Erdos23GapGBBinaryLayerAuto.lean
```

The headline theorem prints only
`[propext, Classical.choice, Quot.sound]`.  There is no `sorry`, `axiom`,
`native_decide`, or private lemma.
