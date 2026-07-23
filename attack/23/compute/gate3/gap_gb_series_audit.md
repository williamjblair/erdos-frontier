# Hostile audit: G-B series reduction

Verdict: **PASS for the quantified series lemma and its interior-bridge RL*
corollary.** The full G-B target remains open.

## Dependency tree

1. **Partner-distance range** — PASS.
   - Claim: `1 <= p(d) <= 3`.
   - Kernel: `partnerDistance_pos`, `partnerDistance_le_three`.
   - Independent check: every positive `d<=96`, all parity branches.

2. **Four-terminal cut inequality** — PASS.
   - Claim: `sep(w1,x2) <= sep(w1,x1)+sep(x1,w2)+sep(w2,x2)`.
   - Kernel: `separation_le_series` by explicit Boolean case split.
   - Independent check: all 16 assignments.

3. **Root/stub swap** — PASS.
   - Claim: the symmetric rooted cut condition is invariant under swapping
     its terminal names.
   - Kernel: `separation_comm`, `rootedCutCondition_swapTerminals`.

4. **Cutwise series validity** — PASS.
   - Claim: two rooted-valid blocks plus the bridge produce a rooted-valid
     series composite.
   - Kernel: `rootedCutCondition_series`.
   - Exact graph replay: all 16,384 cuts of the `n=14` fixture and all
     131,072 cuts of the mixed-distance `n=17` fixture.

5. **Metric and slack decomposition** — PASS.
   - A sole inter-block bridge cannot shorten an internal distance, the
     global stub distance is `d1+1+d2`, Gamma is additive, and slack adds.
   - Kernel arithmetic: `series_slack_identity`.
   - Exact graph replay: both fixtures, including internal distance lists
     `[4,4]` and `[4,6]`.

6. **RL budget superadditivity** — PASS.
   - Kernel: `rlBudget_series_superadditive` and
     `gamma_series_le_rlBudget`.
   - Producer: 17,842,176 exact parameter tuples.
   - Independent verifier: 5,760,000 exact parameter tuples.
   - Minimum margin is zero, attained when both slacks are zero; the theorem
     correctly permits equality.

7. **Strict induction-size gate** — PASS.
   - Claim: if both component sizes are at least four, each minimal
     composite has fewer vertices than the whole series composite.
   - Kernel: `minimalComposite_sizes_lt_series`.
   - No non-strict `<=n` substitution is used.

8. **Bridge extraction from an existing rooted instance** — PASS at paper
   level, using already-proved repository nodes.
   - `IsBridge` on a corridor edge implies no M-edge crosses it
     (`lemma_rl_proof.md` section 4.5; Lean bridge-cut infrastructure is in
     `Erdos23GapGA.lean`).
   - Restrict RFC with the bridge endpoint omitted; use symmetric RFC to
     orient the left block, then swap its terminals.
   - This node is not advertised as a new standalone graph theorem in the
     Lean module; the new cutwise and numerical obligations are kernel
     checked separately.

## Falsification boundaries

- `n>=14`, `|M|>=2`: explicit `n=14`, two-edge fixture passes.
- Mixed even distances: explicit `[4,6]` fixture passes.
- Strict middle regime: both fixtures satisfy `2sp(d)<(d+1)^2` exactly.
- Shared load / forced hub: no per-vertex charging statement occurs.
- Path-packing witness: no L1 volume inequality occurs.
- Equality family: zero-slack series margins are allowed; no strict slack is
  asserted.
- Endpoint bridges: excluded explicitly by `d1,d2>=1`.
- Small opposite component: excluded explicitly by `n1,n2>=4` for the
  strict induction application; the series lemma itself has no such size
  restriction.

## Kernel gate

`Erdos23GapGBSeriesAudit.lean` reports only
`[propext, Classical.choice, Quot.sound]` (some arithmetic nodes need a
subset). No `native_decide`, private lemma, axiom, `sorry`, or theorem-strength
placeholder is used.

## Remaining gap

The audit does **not** certify all G-B. After this reduction the exact open
case is RL* in the original middle regime, with `|M|>=2`, under the added
restriction that every interior bridge of a stub geodesic has a component of
order at most three. Bridge-free corridor segments still require a genuine
multiplicity aggregation argument.
