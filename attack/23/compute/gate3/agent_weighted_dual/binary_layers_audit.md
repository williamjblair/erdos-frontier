# Hostile audit: binary BFS layers with level-aligned demands

Verdict: **PASS for the stated proper subregime. BF-RL and full RL* remain
open.**

The kernel headline is
`Erdos23GapGBBinaryLayers.totalCost_le_rlBudget_of_binaryBfsLayers_levelAligned`.
It assumes literal level alignment for every internal demand and an exact
binary adjacent-layer profile. Neither property is inferred for a general
BF-RL instance.

## Exact statement and definitions

Fix a finite simple supply graph `G`, root `w`, stub `x0`, internal-demand
endpoints `m1 i,m2 i`, a natural level function `ell`, and `d,s`. There are
`d` level gaps, indexed by `r : Fin d`. The upper cut at gap `r` is

```text
T_r = {v : r < ell(v)}.
```

For zero-one functions `active,high : Fin d -> Nat`, the hypotheses are:

1. every supply edge changes level by exactly one;
2. the adjacent layer product is exactly
   `|L_r| |L_{r+1}| = 1 + active_r + 2 high_r`;
3. `active_r <= 1` and `high_r <= active_r`;
4. `ell(w)=0`, `ell(x0)=d`, and every demand endpoint has level at most `d`;
5. rooted RFC holds on every root-excluding finite cut;
6. every demand is legal, `D_i=dist_G(m1_i,m2_i)>=4`;
7. literal alignment holds:
   `D_i = |ell(m1_i)-ell(m2_i)|`;
8. writing `L=sum active` and `H=sum high`,
   `H<=L`, `L+H<=2s`, and `H+1<=s`.

In an ordinary binary BFS profile, each layer has size one or two. Then
`active_r` records that at least one adjacent layer is doubled and `high_r`
records that both are doubled. The displayed profile is respectively
`1,2,4`. The count laws follow from at most `s` doubled levels: an active
gap contributes one incidence, a high gap contributes the second, and the
number of adjacent `11` pairs is at most the number of ones minus one. These
finite count laws are explicit theorem hypotheses; no unquantified
"essentially binary" assertion is used.

## Dependency tree

1. **Simplicity / cut capacity — PASS.**
   `cutSize_levelUpperCut_le_layerProduct` proves

   ```text
   cutSize_G(T_r) <= |L_r| |L_{r+1}|.
   ```

   Every crossing neighbor pair must have levels exactly `r,r+1`; the
   injection is the actual simple-graph adjacency relation, so parallel
   edges are not silently allowed. Combining with the exact layer product
   gives `cutSize_G(T_r) <= 1+active_r+2high_r`.

2. **RFC reserve — PASS.**
   Since `w` is outside `T_r` and `x0` is inside it, RFC consumes one unit:

   ```text
   sum_i cross(i,r) + 1 <= cutSize_G(T_r).
   ```

   Hence the demand-column load is at most
   `active_r+2high_r`, namely `0`, `1`, or `3`.

3. **Alignment / layer cake — PASS.**
   `sum_thresholdSeparation_eq_dist` gives that the number of thresholds
   separating two endpoint levels is their natural distance. The explicit
   alignment hypothesis converts this level span into the graph distance
   `D_i`. Endpoints are explicitly bounded by `d`; vertices not incident
   with a demand may lie beyond level `d`.

4. **Pair-load aggregation — PASS.**
   Expanding `(sum_r cross(i,r))^2` counts ordered pairs of crossed gaps. For
   gaps `r,q`, the common row count is at most both column capacities. If
   either gap is inactive it is zero; if both are active it is at most one
   unless both are high, when it is at most three. Kernel theorem:
   `pairLoad_le_binaryPairCapacity`. Summation gives

   ```text
   sum_i D_i^2 <= L^2 + 2H^2,
   sum_i D_i   <= L + 2H.
   ```

5. **Constant term — PASS.**
   Legality `D_i>=4` gives `4|M|<=sum_i D_i`. Therefore

   ```text
   4 sum_i (D_i+1)^2
     <= 4L^2 + 8H^2 + 9L + 18H.
   ```

   This is proved inside
   `totalCost_le_rlBudget_of_binaryLayerAlignedMatrix`; no fractional
   cardinality is used.

6. **Arithmetic envelope — PASS.**
   `binaryLayer_intervalEnvelope` proves from
   `L<=d`, `H<=L`, `L+H<=2s`, `H+1<=s` that

   ```text
   4L^2 + 8H^2 + 9L + 18H
     <= 4s^2 + 8sd + 16s.
   ```

   `L<=d` is derived in the graph theorem by summing `active_r<=1` over
   `Fin d`. The proof is exact natural-number arithmetic.

7. **Landing in RL — PASS.**
   `parityIndependentBudget_le_rlBudget` uses only `partnerDistance(d)>=1`:

   ```text
   s^2 + 2sd + 4s <= rlBudget(s,d).
   ```

   Multiplication by four and cancellation close the target.

## Exact obstruction to removing alignment

`audit_unaligned_fixture.py` enumerates all `2^14` cuts using integer
arithmetic. Its supply graph has edges

```text
(0,1),(0,8),(1,2),(1,9),(2,3),(2,8),(2,10),(3,4),(3,9),
(4,5),(4,10),(4,12),(5,6),(5,11),(5,13),(6,7),(6,12),
(7,13),(8,9),(10,11),(12,13).
```

Take `w=0`, `x0=7`, and demands `(9,11),(7,10)`. The script verifies:

```text
n=14, d=7, s=6, Gamma=50, rlBudget=144;
all seven corridor edges are nonbridges;
B union M is simple and triangle-free;
RFC minimum slack is zero;
levels are [0,1,2,3,4,5,6,7,1,2,3,4,5,6].
```

Both demands have graph distance four, but `(9,11)` has level span two.
Thus even a fully nonbridge residual instance with binary levels need not
have aligned demands. Any extension must pay the exact detour excess
`D_i-|ell(m1_i)-ell(m2_i)|`; deleting `haligned` is invalid.

## Mandatory falsification record

- **Balanced odd-cycle blow-ups:** the theorem makes no unrestricted claim.
  Its tight `d=1` members lie outside the residual, while dense demands need
  not satisfy the binary profile.
- **Long odd cycles:** single-edge equality is not reused; the theorem is a
  direct RFC aggregation under its stated profile.
- **n=8 forced hub:** no per-vertex load appears.
- **n=12 path-packing witness:** no volume or unit-congestion assertion
  appears. Columns may carry three demands on a high gap.
- **Mixed distances:** distances may vary; only legality and exact alignment
  are required.
- **Vertices beyond level d:** permitted only when they are not demand
  endpoints; this endpoint restriction is explicit in Lean.

## Reproduction and kernel gate

```text
python3 compute23/gate3/agent_weighted_dual/audit_unaligned_fixture.py
lake env lean ErdosProblems/Erdos23GapGBBinaryLayers.lean
```

The Lean module reports only `[propext, Classical.choice, Quot.sound]` or
subsets for every printed theorem. There is no `sorry`, private lemma,
`axiom`, `native_decide`, or floating-point proof dependency.

## Exact remaining gap

For a general valid BF-RL instance, prove a bound for the detour excesses

```text
q_i = (D_i - |ell(m1_i)-ell(m2_i)|) / 2
```

that, together with the proved level-cut matrix bound, pays

```text
sum_i 2 q_i (D_i + |ell(m1_i)-ell(m2_i)| + 2)
```

inside the unused RL budget. This is strictly narrower than restating
BF-RL: the aligned case is exactly `q_i=0` and is closed above.
