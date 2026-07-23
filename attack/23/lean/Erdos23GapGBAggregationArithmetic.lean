/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair, OpenAI Codex
-/
import ErdosProblems.Erdos23GapGBJoint

/-!
# Erdős 23 G-B: aggregation arithmetic and strict completion gate

This module banks the arithmetic interfaces used by two proper BF-RL
subregimes.

The first theorem closes the case in which demands are housed in disjoint
off-corridor components, with at most one demand per component.  The remaining
theorems record the exact order arithmetic and strict-induction gate for the
paper-level private-path completion.

Important scope boundary: this file does **not** construct a `SimpleGraph`
private-path completion and does not prove its connectivity, bipartiteness,
triangle-freeness, cut condition, or distance preservation.  The theorem
`cutCondition_of_privatePathPayments` is only the final finite-sum inequality
after edge-disjoint path payments have separately been supplied.  Therefore
the graph construction is not advertised as kernel-formalized here.
-/

open scoped BigOperators

namespace Erdos23GapGBAggregationArithmetic

open Erdos23GapGBJoint
open Erdos23GapGBSeries

/-- If every demand is housed in a disjoint vertex resource of order at least
its geodesic order, the `s^2` part of the RL budget pays all demands.

In the graph application, `resource i` is the order of the off-corridor
component containing demand `i`.  The graph hypotheses supplying `hpack` and
`hdistance` are intentionally outside this arithmetic theorem. -/
theorem totalCost_le_rlBudget_of_disjoint_componentResources
    {I : Type*} [Fintype I] (D resource : I → ℕ) (s d : ℕ)
    (hpack : (∑ i : I, resource i) ≤ s)
    (hdistance : ∀ i, D i + 1 ≤ resource i) :
    (∑ i : I, (D i + 1) ^ 2) ≤ rlBudget s d := by
  let R := ∑ i : I, resource i
  have hterm : ∀ i, (D i + 1) ^ 2 ≤ resource i ^ 2 := by
    intro i
    exact Nat.pow_le_pow_left (hdistance i) 2
  have hsumTerm : (∑ i : I, (D i + 1) ^ 2) ≤
      ∑ i : I, resource i ^ 2 := by
    exact Finset.sum_le_sum fun i _ => hterm i
  have hsquares : (∑ i : I, resource i ^ 2) ≤ R ^ 2 := by
    simpa [R] using
      (Finset.sum_sq_le_sq_sum_of_nonneg
        (s := (Finset.univ : Finset I)) (f := resource)
        (fun _ _ => Nat.zero_le _))
  have hRsq : R ^ 2 ≤ s ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hpack hpack
  have hsBudget : s ^ 2 ≤ rlBudget s d := by
    unfold rlBudget
    nlinarith [partnerDistance_pos d]
  exact hsumTerm.trans (hsquares.trans (hRsq.trans hsBudget))

/-- Exact numeric order claimed by the paper private-path completion: retain
every distinct demand endpoint and insert `D_i - 1` private internal vertices
on the path assigned to demand `i`.  This definition alone is not a graph
constructor. -/
def privatePathOrder {I : Type*} [Fintype I]
    (endpointCount : ℕ) (D : I → ℕ) : ℕ :=
  endpointCount + ∑ i : I, (D i - 1)

/-- In excess coordinates `D_i = x_i + 4`, the claimed private-completion
order is the exact cross-term `endpointCount + ∑ x_i + 3 |I|`. -/
theorem privatePathOrder_eq_excessCrossTerm
    {I : Type*} [Fintype I]
    (endpointCount : ℕ) (D excess : I → ℕ)
    (hD : ∀ i, D i = excess i + 4) :
    privatePathOrder endpointCount D =
      endpointCount + (∑ i : I, excess i) + 3 * Fintype.card I := by
  have hterm : ∀ i, D i - 1 = excess i + 3 := by
    intro i
    rw [hD i]
    omega
  unfold privatePathOrder
  calc
    endpointCount + ∑ i : I, (D i - 1) =
        endpointCount + ∑ i : I, (excess i + 3) := by
          apply congrArg (endpointCount + ·)
          apply Finset.sum_congr rfl
          intro i _
          exact hterm i
    _ = endpointCount + (∑ i : I, excess i) +
        3 * Fintype.card I := by
          simp [Finset.sum_add_distrib]
          omega

/-- Abstract final cut-count landing: if a separately constructed family of
edge-disjoint supply paths pays every crossing demand, summing the individual
payments proves the cut inequality.  No paths or graph are constructed by this
theorem. -/
theorem cutCondition_of_privatePathPayments
    {I : Type*} [Fintype I]
    (mCross pathCross : I → ℕ) (extraSupply : ℕ)
    (hpay : ∀ i, mCross i ≤ pathCross i) :
    (∑ i : I, mCross i) ≤
      (∑ i : I, pathCross i) + extraSupply := by
  calc
    (∑ i : I, mCross i) ≤ ∑ i : I, pathCross i := by
      exact Finset.sum_le_sum fun i _ => hpay i
    _ ≤ (∑ i : I, pathCross i) + extraSupply := Nat.le_add_right _ _

/-- In the strict RL residual, a completion whose order-square fits the RL
budget is automatically a strict subinstance.  This proves only the numeric
size gate; graph validity must be established separately. -/
theorem completionOrder_lt_ambient_of_sq_le_rlBudget
    {n s d completionOrder : ℕ}
    (hsize : n = d + 1 + s)
    (hresidual : 2 * s * partnerDistance d < (d + 1) ^ 2)
    (hfit : completionOrder ^ 2 ≤ rlBudget s d) :
    completionOrder < n := by
  have hbudget : rlBudget s d < n ^ 2 := by
    unfold rlBudget
    rw [hsize]
    nlinarith
  have hsquare : completionOrder ^ 2 < n ^ 2 := hfit.trans_lt hbudget
  nlinarith

/-- Once a separately justified induction theorem supplies a Gamma bound on a
valid completion, its square-fit condition closes the target cost.  This is
pure transitivity and does not supply the induction premise. -/
theorem totalCost_le_rlBudget_of_completion
    {I : Type*} [Fintype I] (cost : I → ℕ)
    (completionOrder s d : ℕ)
    (hGamma : (∑ i : I, cost i) ≤ completionOrder ^ 2)
    (hfit : completionOrder ^ 2 ≤ rlBudget s d) :
    (∑ i : I, cost i) ≤ rlBudget s d :=
  hGamma.trans hfit

/-- The large-order BF frontier has an absolute RL budget floor.  This uses
only `n = d+1+s`, `n >= 14`, `s >= 5`, and positive terminal distance; the
strict-residual and nonbridge hypotheses are not needed.

The only arithmetically delicate corner is `(s,d)=(5,8)`, where the exact
partner distance is two. -/
theorem rlBudget_ge_135_of_large_frontier
    {n s d : ℕ} (hsize : n = d + 1 + s)
    (hn : 14 ≤ n) (hs : 5 ≤ s) (hd : 1 ≤ d) :
    135 ≤ rlBudget s d := by
  have hp := partnerDistance_pos d
  by_cases hs9 : 9 ≤ s
  · unfold rlBudget
    nlinarith
  · have hsCases : s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
    rcases hsCases with rfl | rfl | rfl | rfl
    · by_cases hd8 : d = 8
      · subst d
        norm_num [rlBudget, partnerDistance]
      · have hd9 : 9 ≤ d := by omega
        unfold rlBudget
        nlinarith
    · have hd7 : 7 ≤ d := by omega
      unfold rlBudget
      nlinarith
    · have hd6 : 6 ≤ d := by omega
      unfold rlBudget
      nlinarith
    · have hd5 : 5 ≤ d := by omega
      unfold rlBudget
      nlinarith

/-- Consequently every separately valid exact completion of order at most
eleven automatically passes the square-fit gate on the large BF frontier. -/
theorem completion_sq_le_rlBudget_of_order_le_eleven
    {n s d completionOrder : ℕ} (hsize : n = d + 1 + s)
    (hn : 14 ≤ n) (hs : 5 ≤ s) (hd : 1 ≤ d)
    (horder : completionOrder ≤ 11) :
    completionOrder ^ 2 ≤ rlBudget s d := by
  have hfloor := rlBudget_ge_135_of_large_frontier hsize hn hs hd
  nlinarith

/-- In particular the distance-four multiplicity-two odd-cycle completion
has order ten and cannot survive into the `n >= 14, s >= 5` gate complement.
This is the exact dispatch for every small-corpus failure profile. -/
theorem doubleDistanceFour_completion_fits_large_frontier
    {n s d : ℕ} (hsize : n = d + 1 + s)
    (hn : 14 ≤ n) (hs : 5 ≤ s) (hd : 1 ≤ d) :
    10 ^ 2 ≤ rlBudget s d := by
  exact completion_sq_le_rlBudget_of_order_le_eleven
    hsize hn hs hd (by omega)

/-- Numeric order of the paper completion for two distinct even distances
`smaller < larger`: a path of length `larger` plus `smaller/2` singleton
two-edge detours.  This is only the order formula, not the graph constructor. -/
def distinctTwoDistanceCompletionOrder (smaller larger : ℕ) : ℕ :=
  larger + 1 + smaller / 2

@[simp]
theorem distinctTwoDistanceCompletionOrder_four_eight :
    distinctTwoDistanceCompletionOrder 4 8 = 11 := by
  decide

/-- The dangerous `(4,8)` distance profile has an order-eleven exact paper
completion, so its square fits throughout the large frontier. -/
theorem fourEight_completion_fits_large_frontier
    {n s d : ℕ} (hsize : n = d + 1 + s)
    (hn : 14 ≤ n) (hs : 5 ≤ s) (hd : 1 ≤ d) :
    (distinctTwoDistanceCompletionOrder 4 8) ^ 2 ≤ rlBudget s d := by
  rw [distinctTwoDistanceCompletionOrder_four_eight]
  exact completion_sq_le_rlBudget_of_order_le_eleven
    hsize hn hs hd (by omega)

/-- Numeric order of the paper two-lane completion for two equal copies of
an even distance.  Again this definition does not construct the graph. -/
def equalTwoDistanceCompletionOrder (distance : ℕ) : ℕ :=
  3 * distance / 2 + 2

@[simp]
theorem equalTwoDistanceCompletionOrder_four :
    equalTwoDistanceCompletionOrder 4 = 8 := by
  decide

/-- A scaled convex-corner estimate for two ordered nonnegative costs. -/
private theorem convexCorner_scaled
    {x y X Y M : ℕ}
    (hxy : x ≤ y) (hy : 2 * y ≤ Y) (hsum : x + y ≤ M)
    (hbalance : X + Y = 2 * M) :
    4 * (x ^ 2 + y ^ 2) ≤ X ^ 2 + Y ^ 2 := by
  by_cases hx : 2 * x ≤ X
  · have hxsq := Nat.pow_le_pow_left hx 2
    have hysq := Nat.pow_le_pow_left hy 2
    nlinarith
  · have hXx : X < 2 * x := by omega
    let u := 2 * x - X
    let v := Y - u
    have huEq : X + u = 2 * x := by
      dsimp [u]
      omega
    have hYu : 2 * y + u ≤ Y := by
      dsimp [u]
      omega
    have huv : u + v = Y := by
      dsimp [v]
      omega
    have hyv : 2 * y ≤ v := by omega
    have hXv : X ≤ v := by omega
    have hxsq : (2 * x) ^ 2 = (X + u) ^ 2 := by rw [huEq]
    have hysq : (2 * y) ^ 2 ≤ v ^ 2 := Nat.pow_le_pow_left hyv 2
    have hmul : u * X ≤ u * v := Nat.mul_le_mul_left u hXv
    nlinarith

/-- Convert a scaled convex-corner bound into the desired unscaled cost. -/
private theorem pairCosts_le_of_scaledCorner
    {A B X Y M R : ℕ}
    (hAB : A ≤ B)
    (hY : 2 * (2 * B + 1) ≤ Y)
    (hM : (2 * A + 1) + (2 * B + 1) ≤ M)
    (hbalance : X + Y = 2 * M)
    (hbudget : X ^ 2 + Y ^ 2 ≤ 4 * R) :
    (2 * A + 1) ^ 2 + (2 * B + 1) ^ 2 ≤ R := by
  have hcorner := convexCorner_scaled
    (x := 2 * A + 1) (y := 2 * B + 1)
    (X := X) (Y := Y) (M := M) (by omega) hY hM hbalance
  nlinarith

/-- Continuous square comparison used away from the sole `s = 5` corner. -/
private theorem oneFour_scaledBudget_of_six
    {s d p : ℕ}
    (hp : 1 ≤ p) (hs : 6 ≤ s) (hn : 13 ≤ s + d)
    (hd : 3 ≤ d) (hds : d < 2 * s) :
    100 + (2 * s + d + 2) ^ 2 ≤
      4 * (s * (2 * d + 2 + s) + 2 * s * p) := by
  nlinarith

/-- Exact convex landing for the complete two-demand BF residual.

Write the two even internal distances as `2*A <= 2*B`.  The larger-edge SE2
bound and the single joint linear estimate

`2*A + 2*B <= s + d + p(d) - 1`

imply the full quadratic RL budget.  Thus the graph-theoretic remainder for
`|M|=2` is isolated to that explicit joint distance-sum estimate; this
theorem does not assert it from RFC. -/
theorem twoEvenCosts_le_rlBudget_of_jointDistanceSum
    {A B s d : ℕ}
    (hA : 2 ≤ A) (hAB : A ≤ B)
    (hSE2 : 4 * B ≤ 2 * s + d)
    (hjoint : 2 * A + 2 * B ≤
      s + d + partnerDistance d - 1)
    (hs : 5 ≤ s) (hn : 13 ≤ s + d)
    (hd : 3 ≤ d) (hds : d < 2 * s)
    (hresidual : 2 * s * partnerDistance d < (d + 1) ^ 2) :
    (2 * A + 1) ^ 2 + (2 * B + 1) ^ 2 ≤ rlBudget s d := by
  have hd1 : d ≠ 1 := by omega
  have hsCases : s % 2 = 0 ∨ s % 2 = 1 := by omega
  have hdCases : d % 4 = 0 ∨ d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 := by
    omega
  rcases hsCases with hs0 | hs1 <;>
    rcases hdCases with hd0 | hd1mod | hd2 | hd3
  · have hpEq : partnerDistance d = 2 := by
      simp [partnerDistance, hd1, show d % 2 = 0 by omega]
    have hY : 2 * (2 * B + 1) ≤ 2 * s + d + 2 := by omega
    have hM : (2 * A + 1) + (2 * B + 1) ≤ s + d + 2 := by
      rw [hpEq] at hjoint
      omega
    have hgap : d + 4 ≤ 2 * s := by omega
    have hmul := Nat.mul_le_mul_left d hgap
    have hbudget : (d + 2) ^ 2 + (2 * s + d + 2) ^ 2 ≤
        4 * rlBudget s d := by
      unfold rlBudget
      rw [hpEq]
      nlinarith [hmul]
    exact pairCosts_le_of_scaledCorner hAB hY hM (by omega) hbudget
  · have hpEq : partnerDistance d = 1 := by
      simp [partnerDistance, hd1, show d % 2 ≠ 0 by omega]
    have hY : 2 * (2 * B + 1) ≤ 2 * s + d + 1 := by omega
    have hM : (2 * A + 1) + (2 * B + 1) ≤ s + d + 1 := by
      rw [hpEq] at hjoint
      omega
    have hgap : d + 3 ≤ 2 * s := by omega
    have hmul := Nat.mul_le_mul_left d hgap
    have hbudget : (d + 1) ^ 2 + (2 * s + d + 1) ^ 2 ≤
        4 * rlBudget s d := by
      unfold rlBudget
      rw [hpEq]
      nlinarith [hmul]
    exact pairCosts_le_of_scaledCorner hAB hY hM (by omega) hbudget
  · have hpEq : partnerDistance d = 2 := by
      simp [partnerDistance, hd1, show d % 2 = 0 by omega]
    have hY : 2 * (2 * B + 1) ≤ 2 * s + d := by omega
    have hM : (2 * A + 1) + (2 * B + 1) ≤ s + d + 2 := by
      rw [hpEq] at hjoint
      omega
    have hgap : d + 2 ≤ 2 * s := by omega
    have hmul := Nat.mul_le_mul_left d hgap
    have hbudget : (d + 4) ^ 2 + (2 * s + d) ^ 2 ≤
        4 * rlBudget s d := by
      unfold rlBudget
      rw [hpEq]
      nlinarith [hmul]
    exact pairCosts_le_of_scaledCorner hAB hY hM (by omega) hbudget
  · have hpEq : partnerDistance d = 1 := by
      simp [partnerDistance, hd1, show d % 2 ≠ 0 by omega]
    have hY : 2 * (2 * B + 1) ≤ 2 * s + d := by omega
    have hM : (2 * A + 1) + (2 * B + 1) ≤ s + d + 1 := by
      rw [hpEq] at hjoint
      omega
    have hgap : d + 1 ≤ 2 * s := by omega
    have hmul := Nat.mul_le_mul_left d hgap
    have hbudget : (d + 2) ^ 2 + (2 * s + d) ^ 2 ≤
        4 * rlBudget s d := by
      unfold rlBudget
      rw [hpEq]
      nlinarith [hmul]
    exact pairCosts_le_of_scaledCorner hAB hY hM (by omega) hbudget
  · have hpEq : partnerDistance d = 2 := by
      simp [partnerDistance, hd1, show d % 2 = 0 by omega]
    have hY : 2 * (2 * B + 1) ≤ 2 * s + d := by omega
    have hM : (2 * A + 1) + (2 * B + 1) ≤ s + d + 3 := by
      rw [hpEq] at hjoint
      omega
    have hgap : d + 2 ≤ 2 * s := by omega
    have hmul := Nat.mul_le_mul_left d hgap
    have hbudget : (d + 6) ^ 2 + (2 * s + d) ^ 2 ≤
        4 * rlBudget s d := by
      unfold rlBudget
      rw [hpEq]
      nlinarith [hmul]
    exact pairCosts_le_of_scaledCorner hAB hY hM (by omega) hbudget
  · have hpEq : partnerDistance d = 1 := by
      simp [partnerDistance, hd1, show d % 2 ≠ 0 by omega]
    have hY : 2 * (2 * B + 1) ≤ 2 * s + d := by omega
    have hM : (2 * A + 1) + (2 * B + 1) ≤ s + d + 2 := by
      rw [hpEq] at hjoint
      omega
    have hgap : d + 1 ≤ 2 * s := by omega
    have hmul := Nat.mul_le_mul_left d hgap
    have hbudget : (d + 4) ^ 2 + (2 * s + d) ^ 2 ≤
        4 * rlBudget s d := by
      unfold rlBudget
      rw [hpEq]
      nlinarith [hmul]
    exact pairCosts_le_of_scaledCorner hAB hY hM (by omega) hbudget
  · have hpEq : partnerDistance d = 2 := by
      simp [partnerDistance, hd1, show d % 2 = 0 by omega]
    have hY : 2 * (2 * B + 1) ≤ 2 * s + d + 2 := by omega
    have hM : (2 * A + 1) + (2 * B + 1) ≤ s + d + 3 := by
      rw [hpEq] at hjoint
      omega
    have hgap : d + 4 ≤ 2 * s := by omega
    have hmul := Nat.mul_le_mul_left d hgap
    have hbudget : (d + 4) ^ 2 + (2 * s + d + 2) ^ 2 ≤
        4 * rlBudget s d := by
      unfold rlBudget
      rw [hpEq]
      nlinarith [hmul]
    exact pairCosts_le_of_scaledCorner hAB hY hM (by omega) hbudget
  · have hpEq : partnerDistance d = 1 := by
      simp [partnerDistance, hd1, show d % 2 ≠ 0 by omega]
    have hY : 2 * (2 * B + 1) ≤ 2 * s + d + 1 := by omega
    have hM : (2 * A + 1) + (2 * B + 1) ≤ s + d + 2 := by
      rw [hpEq] at hjoint
      omega
    have hgap : d + 3 ≤ 2 * s := by omega
    have hmul := Nat.mul_le_mul_left d hgap
    have hbudget : (d + 3) ^ 2 + (2 * s + d + 1) ^ 2 ≤
        4 * rlBudget s d := by
      unfold rlBudget
      rw [hpEq]
      nlinarith [hmul]
    exact pairCosts_le_of_scaledCorner hAB hY hM (by omega) hbudget

/-- Complete convex closure of the two-demand slice in which one internal
distance is exactly four.  If the other even distance is `2*B`, its already
banked per-edge SE2 inequality alone pays both quadratic costs throughout the
strict BF residual.  No joint aggregation hypothesis is used. -/
theorem twoCosts_le_rlBudget_of_oneDistanceFour
    {B s d : ℕ}
    (hB : 2 ≤ B) (hSE2 : 4 * B ≤ 2 * s + d)
    (hs : 5 ≤ s) (hn : 13 ≤ s + d)
    (hd : 3 ≤ d) (hds : d < 2 * s)
    (hresidual : 2 * s * partnerDistance d < (d + 1) ^ 2) :
    25 + (2 * B + 1) ^ 2 ≤ rlBudget s d := by
  have hp : 1 ≤ partnerDistance d := partnerDistance_pos d
  have hlin : 2 * (2 * B + 1) ≤ 2 * s + d + 2 := by omega
  have hsq := Nat.pow_le_pow_left hlin 2
  by_cases hs6 : 6 ≤ s
  · have hbase := oneFour_scaledBudget_of_six
      (p := partnerDistance d) hp hs6 hn hd hds
    unfold rlBudget
    nlinarith
  · have hsEq : s = 5 := by omega
    subst s
    have hdCases : d = 8 ∨ d = 9 := by omega
    rcases hdCases with rfl | rfl
    · have hB4 : B ≤ 4 := by omega
      interval_cases B <;> norm_num [rlBudget, partnerDistance]
    · have hB4 : B ≤ 4 := by omega
      interval_cases B <;> norm_num [rlBudget, partnerDistance]

#print axioms totalCost_le_rlBudget_of_disjoint_componentResources
#print axioms privatePathOrder_eq_excessCrossTerm
#print axioms cutCondition_of_privatePathPayments
#print axioms completionOrder_lt_ambient_of_sq_le_rlBudget
#print axioms totalCost_le_rlBudget_of_completion
#print axioms rlBudget_ge_135_of_large_frontier
#print axioms completion_sq_le_rlBudget_of_order_le_eleven
#print axioms doubleDistanceFour_completion_fits_large_frontier
#print axioms distinctTwoDistanceCompletionOrder_four_eight
#print axioms fourEight_completion_fits_large_frontier
#print axioms equalTwoDistanceCompletionOrder_four
#print axioms twoEvenCosts_le_rlBudget_of_jointDistanceSum
#print axioms twoCosts_le_rlBudget_of_oneDistanceFour

end Erdos23GapGBAggregationArithmetic
