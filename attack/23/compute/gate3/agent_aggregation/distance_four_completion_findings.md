# Shared completion for the exact distance-four slice

Status: **proved paper construction and exact executable audit; not full
BF-RL and not yet a Lean graph construction**.

Let `M` be a triangle-free demand graph on its `r` non-isolated endpoints,
and suppose every demand has required distance exactly four.  Fix a proper
edge coloring `c:E(M)→{1,...,k}`.

Construct a bipartite supply graph with:

- one endpoint vertex `u` for every demand endpoint;
- one port `p_u` for every endpoint;
- one center `z_j` for every used edge color.

For a demand `uv` of color `j`, add the path

```text
u -- p_v -- z_j -- p_u -- v.
```

The exact order is

```text
N_4 = 2r+k.
```

## Validity proof

The endpoint and center vertices form one bipartition side; ports form the
other.  Properness of the edge coloring makes all four supply edges assigned
to distinct demands pairwise distinct: an edge `p_v z_j` can recur only for
two color-`j` demands incident with `v`, which properness forbids.  Therefore
every cut-crossing demand is injectively paid by a crossing edge of its own
four-path, proving S2.

For a demand `uv`, a two-edge supply path would require a common port
`p_x`, hence demands `ux` and `vx`.  Together with `uv` these form a demand
triangle, impossible.  The supply graph is bipartite and contains the
displayed four-path, so its `u,v` distance is exactly four.  Consequently
adding `M` creates no triangle.  Remaining supply components may be joined
by bridges between opposite bipartition sides; because a bridge joins old
components, it neither creates a two-edge route for an existing demand nor
invalidates the cut payment.

Thus `(H,M)` is a valid exact completion of order `2r+k`.  Under strict
Gamma induction it closes the distance-four slice whenever

```text
(2r+k)^2 ≤ rlBudget(s,d).
```

This is a proper additional subregime.  It is self-tight on the dense end:
for the `C5[q]` demand graph `K_{q,q}`, `r=2q` and `k=q`, hence `N_4=5q`.
It does not by itself prove that every rooted residual has a coloring whose
order-square fits the RL budget.

`test_distance_four_completion.py` checks every cut, every demand distance,
triangle-freeness, bipartiteness, and exact order for `K_{2,2}`, a five-cycle,
a disconnected matching, and a forced shared-neighbor star.
