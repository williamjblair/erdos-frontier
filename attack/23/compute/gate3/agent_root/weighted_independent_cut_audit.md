# Dead route: weighted independent-set cut

## Verdict

The proposed direct sufficient statement

```text
max { sum(deg(v)) : I is an independent set } >= e(G) - n^2/25
```

is false for triangle-free graphs.  The connected cubic graph on eight
vertices with supply edges

```text
03,04,14,05,15,25,16,26,36,27,37,47
```

has maximum independent degree-sum `9`, whereas
`e-n^2/25 = 12-64/25 = 236/25 > 9`.  Exhaustion of all `2^8` subsets is
performed by `weighted_independent_cut_counterexample.py` and protected by
its pytest regression.

This does not refute Erdős #23.  Exhaustion of the same `2^8` cuts gives
maximum cut `10`, hence bipartization number `2 < 64/25`.  The missing unit
of cut value comes from a non-star cut that is not the edge boundary of an
independent set.

The fixture was first found by exact `geng -ct 8` enumeration (graph6
`GCrb\`o`), then reduced to the literal edge-list checker above.  No graph6
parser, randomness, floating point, or solver is a proof dependency.

## Consequence

Weighted independence may remain a lower-bound ingredient, but replacing
maximum cut by the best independent-set cut loses too much even at order
eight.  No proof of #23 may use the displayed sufficient statement.
