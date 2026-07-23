# Hostile audit: BF-RL two-demand distance-four slice

Verdict: **PASS for the exact graph-level slice with two internal demands
and one internal distance equal to four.** This does not close the case in
which both distances are at least six, any family of three or more demands,
all BF-RL, the multi-stub induction, or the connected core.

## Dependency tree

The kernel source is
`ErdosProblems/Erdos23GapGBTwoDemand.lean`.

1. `symmetricRootedCutCondition_of_rootForm` converts root-excluding RFC to
   its all-cuts form without changing a cut count.
2. Nonnegativity of the other demand term shows that this family condition
   contains the root--stub pair plus either selected internal demand. This
   is `twoDemandCutCondition_of_rootedCutCondition`.
3. A shortest path for the selected demand and the closed G-A theorem
   `gapGA_symmetric_bounds` give the exact per-edge bound
   `2D <= 2s+d`. This is
   `two_mul_dist_le_twice_slack_add_length_of_rootedCutCondition`.
4. Proper bipartite coloring makes the other internal distance even. If it
   is `2B`, legality gives `B>=2`, and step 3 gives `4B<=2s+d`.
5. The repaired integer theorem
   `twoCosts_le_rlBudget_of_oneDistanceFour` proves
   `25+(2B+1)^2 <= rlBudget(s,d)` throughout the strict BF residual.
6. `Fin.sum_univ_two` identifies that expression with the two graph costs.
   The indexed theorem is
   `totalCost_le_rlBudget_of_twoDemands_oneDistanceFour`; reindexing by
   `Fin.rev` gives the index-free headline
   `totalCost_le_rlBudget_of_twoDemands_existsDistanceFour`.

Every node is kernel checked with only
`[propext, Classical.choice, Quot.sound]`.

## Boundary and falsification checks

- The theorem retains the strict residual hypotheses `s>=5`, `d>=3`,
  `d<2s`, `s+d>=13`, and `2s*p(d)<(d+1)^2` literally.
- It allows arbitrary shared endpoints and arbitrary overlap of shortest
  paths. No path packing, edge volume, or per-vertex load is asserted.
- The forced-hub double broom has both distances four and is included.
- The mixed `(4,6)` and `(4,8)` profiles are included whenever the exact
  residual hypotheses hold.
- The path-packing witness has four demands and is outside the theorem; no
  inference about it is made.
- Balanced odd-cycle blow-ups either have more than two demands or lie on a
  non-residual/equality boundary; the statement does not claim a stability
  inequality for them.
- The theorem uses the actual graph distance and the actual RFC family sum.
  There is no private graph lemma, asserted joint distance bound, or
  RL-equivalent hypothesis.

## Exact arithmetic reproduction

`two_demand_distance_four_verify.py` independently enumerates every
`5<=s<1000`, `3<=d<2s` satisfying the residual gates. For each row it tests
the largest integral `B` satisfying `4B<=2s+d`; monotonicity of
`25+(2B+1)^2` makes this a simultaneous exact check of every smaller legal
integral `B`. That bounded enumeration is falsification support only. The
all-natural-number proof is the Lean theorem, whose repaired proof splits
the relevant residue classes instead of using the false continuous
relaxation.

## Kernel gate

```text
lake env lean ErdosProblems/Erdos23GapGBTwoDemand.lean
```

There is no `sorry`, `axiom`, private theorem, floating-point computation,
or `native_decide`.

## Exact remaining two-demand gap

For a strict-residual rooted instance with exactly two internal demands and
both even distances at least six, prove the RL cost inequality directly or
derive a genuinely weaker geometry-sensitive sufficient inequality.  The
formerly proposed shortcut

```text
D1 + D2 <= s + d + p(d) - 1
```

is false: the exact all-nonbridge `n=76,d=11,s=64,p=1` fixture in
`agent_weighted_dual/joint_distance_counterexample_audit.md` has
`(D1,D2)=(38,38)`.  Its failure does not refute RL.
