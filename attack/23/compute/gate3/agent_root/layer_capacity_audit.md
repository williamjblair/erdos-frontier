# Hostile audit: arbitrary level-cut capacity envelope

Verdict: **PASS for the exact conditional theorem.**  The module supplies a
general quadratic accounting engine for a level-aligned threshold matrix.
It does not establish level alignment or prove the numerical envelope for an
arbitrary graph.

## Dependency tree

1. A product of two zero-one row entries is bounded by either entry.
2. Summing gives
   `pairLoad(r,q) <= min(columnLoad(r),columnLoad(q))`.
3. RFC and a root-stub threshold cut of size at most `c_r+1` give
   `columnLoad(r)<=c_r`.
4. Level alignment expands
   `sum_i D_i^2` as the sum of all pairwise column intersections, hence
   `sum_i D_i^2 <= sum_{r,q} min(c_r,c_q)`.
5. Legality `D_i>=4` gives `4|I|<=sum_i D_i`; expanding the cost yields

   ```text
   4 sum_i (D_i+1)^2
     <= 4 sum_{r,q} min(c_r,c_q) + 9 sum_r c_r.
   ```

6. The explicitly assumed scalar envelope compares that last expression
   with four times the exact RL budget.

The module also kernel-checks the final near-boundary polynomial step.  If a
literal layer profile supplies

```text
Q + 2B + A <= 4s^2,
C = 2s + A,
5A <= 8B + 5(s-1),
```

then either row `d=2s-1` or `d=2s-2` satisfies the required envelope for
every `s>=4`.  These three profile inequalities remain explicit hypotheses;
the theorem does not attribute them to an arbitrary graph.

A simpler specialization uses only `Q<=4s^2` and `C<=2s+2`.  The module
derives the first inequality whenever capacities obey `c_r<=t_r^2` and
`sum t_r<=2s`, and exposes the graph theorem
`totalCost_le_rlBudget_of_nearBoundaryCapacityProfile` with exactly those
inputs.  Structural classification must still provide the weights, the
capacity sum, and level alignment.

All six nodes are kernel theorems in
`ErdosProblems/Erdos23GapGBLayerCapacity.lean` or direct applications of
RFC and the imported threshold-separation identity.

## Scope and falsification checks

- `haligned` is literal graph-distance equality, so the known unaligned
  binary-layer fixture is outside the theorem.
- `hcut` and `henvelope` quantify every column and every ordered column pair;
  no average-capacity or asymptotic phrase is used.
- Capacities may be arbitrary natural numbers.  The theorem does not infer
  them from vertex count, simplicity, or a drawing.
- Mixed distances, shared endpoints, and arbitrary finite multiplicity are
  allowed.  There is no vertex-load or path-packing premise, so the forced-hub
  and path-packing witnesses do not falsify any asserted node.
- The envelope can be too weak on a given profile; in that event the theorem
  simply does not apply.  It is not presented as the missing universal BF-RL
  certificate.

## Kernel gate

```text
lake env lean ErdosProblems/Erdos23GapGBLayerCapacity.lean
```

All printed theorems depend only on
`[propext, Classical.choice, Quot.sound]`.  There is no `sorry`, `axiom`,
`native_decide`, private lemma, or floating-point computation.
