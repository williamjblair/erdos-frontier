# G-B series composition across an interior corridor bridge

Status: **PROVED quantified reduction**, not a proof of all G-B or RL*.

## 1. Exact theorem

Let `R_i=(B_i,M_i,w_i,x_i)` be two valid one-stub rooted instances on
disjoint vertex sets, with positive stub distances `d_i`, slacks `s_i`, and
internal masses `Gamma_i`. Join them by the single new cut-graph edge
`x_1 w_2`; add no inter-block M-edge. The resulting rooted instance has root
`w_1` and stub terminal `x_2`. Then:

1. the series composite is rooted-valid;
2. `d=d_1+d_2+1`, `s=s_1+s_2`, and `Gamma=Gamma_1+Gamma_2`; and
3. if each block satisfies RL, then the composite satisfies RL.

The new content is local to series composition and does not assert a
2-connected reduction.

## 2. Cut proof

Write `sep(a,b)` for the 0/1 indicator that terminals `a,b` are on opposite
sides of a cut. For every cut,

    sep(w_1,x_2)
      <= sep(w_1,x_1) + sep(x_1,w_2) + sep(w_2,x_2).       (S1)

The two local rooted conditions give

    m_i + sep(w_i,x_i) <= b_i.

The global cut counts are exactly

    m = m_1+m_2,
    b = b_1+b_2+sep(x_1,w_2).

Adding the local inequalities and using (S1) proves `m+sep(w_1,x_2)<=b`.
`Erdos23GapGBSeries.rootedCutCondition_series` is the kernel proof. All 16
terminal-membership assignments are also checked independently.

Root/stub orientation causes no hidden condition: symmetric RFC uses only
`sep`, and `separation_comm` plus `rootedCutCondition_swapTerminals` prove the
swap in Lean.

## 3. Exact budget proof

Define

    p(1)=3;
    p(d)=2 for positive even d;
    p(d)=1 for odd d>=3,

and

    F(s,d) = s(2d+2+s) + 2s p(d).

Put `D=d_1+d_2+1` and `P=p(D)`. Direct expansion gives

    F(s_1+s_2,D) - F(s_1,d_1) - F(s_2,d_2)
      = 2s_1(s_2+d_2+1+P-p(d_1))
        + 2s_2(d_1+1+P-p(d_2)).                           (S2)

Both parentheses are nonnegative because `d_i>=1`, `P>=1`, and
`p(d_i)<=3`. Hence the margin is nonnegative. The theorem
`rlBudget_series_superadditive` proves the inequality in Lean; the exact
producer and independent verifier reproduce (S2) over 17,842,176 and
5,760,000 parameter tuples respectively.

## 4. RL* corollary for an existing rooted instance

Let `P` be a `w`-to-`x_0` geodesic in a valid one-stub instance `R`, and let
`ab` be an interior edge of `P`, oriented from `w` toward `x_0`. Assume:

- `ab` is a bridge of `B`;
- deleting it gives components `A` and `C` containing `w` and `x_0`;
- `d_A=dist_B(w,a)>=1`, `d_C=dist_B(b,x_0)>=1`; and
- `|A|,|C|>=4`.

Then this case of RL* is closed under the induction hypothesis that Gamma
holds for all connected valid instances on fewer than `|A|+|C|` vertices.

Proof. The proved bridge lemma in `lemma_rl_proof.md` section 4.5 says no
M-edge crosses `A|C`. Restricting symmetric RFC makes `A` a rooted block with
terminal pair `(w,a)` (first obtain root `a`, stub `w`, then swap), and `C` a
rooted block with pair `(b,x_0)`. Distances inside either component are
unchanged: a path leaving a bridge component cannot return without using the
same bridge twice. Thus Gamma splits exactly and the geodesic gives
`d=d_A+1+d_C`; `series_slack_identity` gives `s=s_A+s_C`.

The minimal composite for block `i` has `n_i+p(d_i)` vertices. Since
`p(d_i)<=3` and the opposite component has at least four vertices,

    n_i+p(d_i) < |A|+|C|.

The strict Gamma induction therefore proves RL for both blocks via the
already-proved minimal-composite equivalence. Apply series budget
superadditivity. `minimalComposite_sizes_lt_series` kernel-checks the strict
size gate.

## 5. Exact boundary fixtures

The producer and independent verifier both check:

- constant-distance boundary: `n=14`, `|M|=2`, `d=9`, `s=4`, M-distances
  `[4,4]`, `Gamma=50`, RL budget `104`; all `2^14=16,384` cuts pass and the
  bridge components have sizes `[7,7]`;
- mixed-distance boundary: `n=17`, `|M|=2`, `d=11`, `s=5`, M-distances
  `[4,6]`, `Gamma=74`, RL budget `155`; all `2^17=131,072` cuts pass and the
  bridge components have sizes `[7,10]`.

Both lie in the strict open middle regime `2sp(d)<(d+1)^2`. The mixed fixture
shows that the reduction makes no constant-distance assumption. It uses no
path-packing, per-vertex load, Holder, Minkowski, or effective-resistance
claim, so the gate-2 killed families are not dependencies.

## 6. Exact frontier change

Any remaining minimal G-B/RL* counterexample has the following additional
property on every chosen stub geodesic: no interior corridor bridge with
positive prefix and suffix distance can leave at least four vertices on both
sides.

Equivalently, the exact remaining quantified lemma is G-B restricted by

    for every interior geodesic edge e,
      IsBridge_B(e) -> min(|A_e|,|C_e|) <= 3.

This restriction is strictly weaker than assuming the entire cut graph is
2-connected. It does not close bridge-free corridor blocks, bridges within
three vertices of an endpoint, or the full multi-edge aggregation.
