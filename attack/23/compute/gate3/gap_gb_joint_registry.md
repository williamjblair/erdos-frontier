# Erdős 23 G-B joint-aggregation registry

Campaign branch: `main`.

## Exact residual target

For a valid one-stub rooted instance `(B,M,w,x0)` on `n` vertices, put
`d=dist_B(w,x0)`, `s=n-1-d`, and
`Gamma=sum_{uv in M}(dist_B(u,v)+1)^2`. After the banked bridge eliminations
and equality/one-defect boundary theorems, the live BF-RL slice is

```text
n >= 14,
5 <= s,
2*s*p(d) < (d+1)^2,
|M| >= 2,
d <= 2*s-2,
some w-x0 geodesic has every edge nonbridge.
```

The target is `Gamma <= s*(2*d+2+s)+2*s*p(d)` under the strict Gamma
induction hypothesis.  A reformulation with equivalent strength is not a
new result.

## Route registry

| ID | Route | Proposed leverage | Initial status |
|---|---|---|---|
| GB-FLOW | RFC flow/cut duality | Sum a weighted laminar family of RFC cuts so every long demand receives quadratic credit while corridor capacity is counted once. | blocked as a proof route: cut domination does not imply multicommodity routing; retained only as BF-RL search context |
| GB-2E | Two-edge joint excess | Prove that two internal edges cannot simultaneously approach the single-edge bounds; test `sum(D_i-4)<=2*s-4` and capacity-corrected variants. | falsification-only: raw excess survives samples but is arithmetically insufficient for BF-RL without a separate multiplicity/cross-term bound |
| GB-2SUM | Two-demand joint distance sum | For ordered even distances `2A<=2B`, derive `2A+2B<=s+d+p(d)-1` from the two-demand RFC geometry, then combine it with SE2 for the larger edge. | **killed:** an exact `n=76,d=11,s=64,p=1,(D1,D2)=(38,38)` strict-residual RFC fixture has an all-nonbridge corridor and `D1+D2=76>75=s+d+p-1`; RL still holds with cost `3042<=5760` |
| GB-2W | Weighted two-demand ledger | Apply G-A to the two internal geodesics as well as the rooted pair, obtaining `Dmin+2Dmax<=2(s+d)` and `2Dmax<=2s+d`, then optimize the feasible polygon. | completed on all `2d<s`; for even `d>=6`, also completed on `2d-3<=s<=2d`; exact remaining slice is odd `d` with `s<=2d`, or even `d` with `s<=2d-4` |
| GB-DEL | Bridge-free deletion/induction | Delete or split at a corridor vertex whose removal preserves a smaller valid instance and quantify the exact distance/mass change. | partial success: every corridor bridge is eliminated; remaining graph is fully corridor-bridge-free with `d<=2s`, `s>=5` |
| GB-END | Endpoint-near series absorption | Extend the banked series theorem when one bridge component has at most three vertices by classifying the finite rooted block and paying its exact budget. | completed: exact gate dispatch, small-block retraction, and arbitrary endpoint-block absorption are proved |
| GB-CUTDUAL | Weighted RFC cut dual | Convert every integer vertex potential into an exact coarea inequality, then seek a finite or laminar weighted-cut certificate majorizing `(D+1)^2` jointly. | single-potential, potential-family, direct weighted-cut, and denominator-cleared rational interfaces completed in Lean; certificate construction for BF-RL remains open and is not counted as closure |
| GB-WIS | Direct weighted independent-set cut | Prove that some independent set has degree-sum at least `e(G)-n^2/25`, so its boundary cut proves #23 directly. | **killed:** the exact connected cubic graph `GCrb\`o` on eight vertices has maximum independent degree-sum `9<236/25`, although its actual maximum cut is 10 |
| GB-EQBOUND | Equality boundary `d=2s` | Use equality in the canonical interval count to force a chain of two-edge blocks, then pack each demand across capacity-two articulations. | completed: the canonical block projection, RFC cuts, capacity bound, parity-corrected distance comparison, and exact RL landing are kernel proved; `d=2s` is removed from BF-RL |
| GB-ONEDEF | One-defect boundary `d=2s-1` | Classify the single interval defect, derive the literal one-high BFS geometry, and apply the binary-layer cut matrix. | completed: mass and overlap profiles, local routing, same-layer diameter, exact alignment, RFC landing, checker, hostile audit, and kernel headline are proved; `d=2s-1` is removed from BF-RL |

## Mandatory falsification fixtures

Every candidate must be checked against:

1. balanced odd-cycle blow-ups at both long-thin and short-fat ends;
2. the `n=8` forced-hub double broom, which kills vertex-load bounds;
3. the `n=12` path-packing witness, which kills unit-congestion and volume aggregation;
4. both banked mixed/constant series fixtures;
5. all exhaustive rooted instances through the stored `n<=11, |M|<=2` corpus;
6. the exact thin-corridor families at `s=2,3`.
7. the exact all-nonbridge `n=76` two-demand fixture, which kills GB-2SUM
   while leaving 2718 units of RL slack.

## Dead routes retained

- Do not use `sum D_i + d <= e(B)`; the `n=12` witness falsifies it.
- Do not sum the individual SE1/SE2 square bounds.
- Do not assign a uniform per-vertex load; the forced hub falsifies it.
- Do not invoke multicommodity routing from the RFC cut condition.
- Do not use order-11 flag algebras or a target-strength aggregation lemma.
- Do not use `D1+D2<=n+p(d)-2` for two demands; the exact `n=76`
  common-endpoint diamond-chain fixture falsifies it inside the live residual.
- Do not replace maximum cut by the best independent-set boundary cut; the
  exact eight-vertex cubic fixture in `agent_root/weighted_independent_cut_audit.md`
  falsifies the required weighted-independence inequality.

## Banked frontier after this campaign

See `gap_gb_joint_findings.md` and `gap_gb_joint_audit.md`. The single open
node is BF-RL on a selected geodesic whose every edge is a nonbridge, with
the additional proved numerical restrictions `s>=5` and `d<=2s-2`.  Its
two-demand slice must be proved at quadratic strength or with a weaker
geometry-sensitive invariant; the former GB-2SUM linear shortcut is false.
The weighted G-A pair closes every two-demand instance with `2d<s`; for
even `d>=6` it also closes the four rows `2d-3<=s<=2d`.  Thus the remaining
two-demand ratio is odd `d` with `s<=2d`, or even `d` with `s<=2d-4`
(with the distance-four subslice independently closed).
