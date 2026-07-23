# Hostile audit: BF-RL isometric size-two cut basis

Verdict: **PASS for the generic cut-basis landing.** This module does not
assert that every BF-RL graph, or even every canonical defect shape, admits
the required cut basis. Constructing it remains a literal graph obligation.

## Dependency tree

The kernel source is
`ErdosProblems/Erdos23GapGBIsometricCuts.lean`.

1. At least two demands and `D_i>=4` imply every selected `D_i` leaves at
   least four units in the total distance sum.
2. If `sum D_i<=d`, then `D_i+1<=d-3`. Convexity and
   `4*|I|<=sum D_i` give the explicit scaled bound

   ```text
   4 * sum_i (D_i+1)^2 <= 5*d*(d-3).
   ```

3. For `d<=2s`, exact natural-number arithmetic gives

   ```text
   5*d*(d-3) <= 4*(s^2+2sd+4s) <= 4*rlBudget(s,d).
   ```

   This is
   `totalCost_le_rlBudget_of_sumDistances_le_length`.
4. The sharper convex form is

   ```text
   sum_i (D_i+1)^2 <= (sum_i D_i-3)^2+25.
   ```

   It follows by writing `D_i=E_i+4` and using
   `sum E_i^2 <= (sum E_i)^2`. Consequently `sum D_i<=2s` lands RL
   throughout `3s<=2d`. Kernel:
   `sum_add_one_sq_le_total_sub_three_sq_add_twentyFive` and
   `totalCost_le_rlBudget_of_sumDistances_le_twiceSlack`.
5. For every cut in the stated basis, symmetric RFC has one unit consumed
   by the root--stub pair and the graph cut has capacity at most two.
   Therefore all internal demands together use at most one unit in that
   column.
6. It is enough that each distance be bounded by its number of separating
   cuts; cuts may repeat. Summing columns gives `sum D_i<=|K|=d`, and step 3
   lands RL. This is
   `totalCost_le_rlBudget_of_dominatingTwoCutBasis`; exact isometry is a
   corollary.

All five headlines report exactly
`[propext, Classical.choice, Quot.sound]`.

## Falsification record

- No cut basis is inferred from RFC, nonbridgeness, or a generic BFS layer
  profile.
- The `n=12` path-packing witness is irrelevant unless it supplies the
  explicit isometric size-two family; no global volume theorem is claimed.
- The forced-hub witness is allowed: the theorem counts cut coordinates,
  not vertex or routed-path load.
- Repeated endpoints and mixed even distances are allowed.
- The hypothesis `|I|>=2` is essential to the `d-3` convex cap and remains
  explicit. The already-banked single-demand theorem handles `|I|=1`.
- A pure-mass application still needs an additional rigidity hypothesis.
  Saturated disjoint intervals alone do **not** force a literal cycle chain:
  exact `s=5,d=8` q2+q2 constructors with optional bipartite attachments
  produce a three-edge Djokovic class, and another option makes the raw
  Djokovic relation nontransitive. Thus no such basis is inferred or
  smuggled into this module.

## Exact arithmetic reproduction

`isometric_cut_basis_verify.py` checks the polynomial comparison over
`5<=s<=1000`, `8<=d<=2s`, with the exact convex extremizer consisting of
distances four and the largest remaining even distance; no failure occurs.
This bounded check is falsification support only. The quantified proof is in
Lean.

## Kernel gate

```text
lake env lean ErdosProblems/Erdos23GapGBIsometricCuts.lean
```

There is no `sorry`, `axiom`, private theorem, floating-point computation,
or `native_decide`.
