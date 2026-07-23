/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair, OpenAI Codex
-/
import ErdosProblems.Erdos23GapGBBinaryLayers

/-!
# Erdős 23 G-B: arbitrary level-cut capacities

For a level-aligned demand family, RFC bounds each threshold-cut column by
its residual supply capacity.  The intersection of any two zero-one columns
is at most the smaller column capacity.  This gives the exact general
quadratic envelope

`4 * sum_{r,q} min(c_r,c_q) + 9 * sum_r c_r`.

Unlike the sharper binary-layer theorem, this result accepts arbitrary
finite capacities.  A graph application must still prove level alignment
and the displayed numerical envelope; neither is inferred here.
-/

namespace Erdos23GapGBLayerCapacity

open scoped BigOperators
open SimpleGraph
open Erdos23GapGA
open Erdos23GapGBJoint
open Erdos23GapGBSeries
open Erdos23GapGBBinaryLayers

/-- Two zero-one columns with capacities `a` and `b` have intersection at
most `min a b`. -/
theorem pairLoad_le_minColumnCapacity
    {I : Type*} [Fintype I] (left right : I → ℕ) (a b : ℕ)
    (hleft01 : ∀ i, left i ≤ 1) (hright01 : ∀ i, right i ≤ 1)
    (hleft : (∑ i : I, left i) ≤ a)
    (hright : (∑ i : I, right i) ≤ b) :
    (∑ i : I, left i * right i) ≤ min a b := by
  have hleLeft : (∑ i : I, left i * right i) ≤ ∑ i : I, left i := by
    exact Finset.sum_le_sum fun i _ => by
      have hi := hright01 i
      nlinarith
  have hleRight : (∑ i : I, left i * right i) ≤ ∑ i : I, right i := by
    exact Finset.sum_le_sum fun i _ => by
      have hi := hleft01 i
      nlinarith
  exact (le_min_iff.mpr ⟨hleLeft.trans hleft, hleRight.trans hright⟩)

/-- The complete bipartite residual capacity between levels with `x` and `y`
extra vertices is bounded by the square of their total extras. -/
theorem adjacentExtraCapacity_le_sum_sq (x y : ℕ) :
    x + y + x * y ≤ (x + y) ^ 2 := by
  by_cases hx : x = 0
  · subst x
    simp only [zero_add, zero_mul, add_zero]
    by_cases hy : y = 0
    · subst y
      norm_num
    · have hy1 : 1 ≤ y := Nat.one_le_iff_ne_zero.mpr hy
      have := Nat.mul_le_mul_left y hy1
      simpa [pow_two] using this
  · have hx1 : 1 ≤ x := Nat.one_le_iff_ne_zero.mpr hx
    have hxx : x ≤ x * x := by
      simpa using Nat.mul_le_mul_left x hx1
    have hyx : y ≤ x * y := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left y hx1
    nlinarith

/-- If capacities are bounded by squares of nonnegative profile weights,
their pairwise minimum is bounded by the product of those weights. -/
theorem min_le_mul_of_le_squares
    {a b x y : ℕ} (ha : a ≤ x ^ 2) (hb : b ≤ y ^ 2) :
    min a b ≤ x * y := by
  rcases le_total x y with hxy | hyx
  · calc
      min a b ≤ a := min_le_left _ _
      _ ≤ x ^ 2 := ha
      _ = x * x := by simp [pow_two]
      _ ≤ x * y := Nat.mul_le_mul_left x hxy
  · calc
      min a b ≤ b := min_le_right _ _
      _ ≤ y ^ 2 := hb
      _ = y * y := by simp [pow_two]
      _ ≤ x * y := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_left y hyx

/-- A total profile weight at most `2s` bounds the complete ordered-pair
minimum envelope by `4s^2`. -/
theorem minColumnEnvelope_le_four_sq
    {R : Type*} [Fintype R] (capacity weight : R → ℕ) (s : ℕ)
    (hcapacity : ∀ r, capacity r ≤ (weight r) ^ 2)
    (hweight : (∑ r : R, weight r) ≤ 2 * s) :
    (∑ r : R, ∑ q : R, min (capacity r) (capacity q)) ≤ 4 * s ^ 2 := by
  calc
    (∑ r : R, ∑ q : R, min (capacity r) (capacity q)) ≤
        ∑ r : R, ∑ q : R, weight r * weight q := by
      exact Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun q _ =>
        min_le_mul_of_le_squares (hcapacity r) (hcapacity q)
    _ = (∑ r : R, weight r) ^ 2 := by
      calc
        (∑ r : R, ∑ q : R, weight r * weight q) =
            ∑ r : R, weight r * (∑ q : R, weight q) := by
              apply Finset.sum_congr rfl
              intro r _
              rw [Finset.mul_sum]
        _ = (∑ r : R, weight r) * (∑ q : R, weight q) := by
              rw [Finset.sum_mul]
        _ = (∑ r : R, weight r) ^ 2 := by simp [pow_two]
    _ ≤ (2 * s) ^ 2 := by
      exact Nat.pow_le_pow_left hweight 2
    _ = 4 * s ^ 2 := by ring

/-- Matrix form of the arbitrary-capacity level-cut bound.

The final hypothesis is a completely explicit scalar inequality in the
column capacities.  It is deliberately kept separate from the graph and is
the only profile-specific arithmetic required by the theorem.
-/
theorem totalCost_le_rlBudget_of_minColumnEnvelope
    {I R : Type*} [Fintype I] [Fintype R]
    (D : I → ℕ) (cross : I → R → ℕ) (capacity : R → ℕ)
    (s d : ℕ)
    (hcross : ∀ i r, cross i r ≤ 1)
    (haligned : ∀ i, D i = ∑ r : R, cross i r)
    (hcolumn : ∀ r, (∑ i : I, cross i r) ≤ capacity r)
    (hlegal : ∀ i, 4 ≤ D i)
    (henvelope :
      4 * (∑ r : R, ∑ q : R, min (capacity r) (capacity q)) +
          9 * (∑ r : R, capacity r) ≤
        4 * rlBudget s d) :
    (∑ i : I, (D i + 1) ^ 2) ≤ rlBudget s d := by
  classical
  let C := ∑ r : R, capacity r
  let Q := ∑ r : R, ∑ q : R, min (capacity r) (capacity q)
  let totalD := ∑ i : I, D i
  let totalDsq := ∑ i : I, (D i) ^ 2
  have hlinear : totalD ≤ C := by
    calc
      totalD = ∑ r : R, ∑ i : I, cross i r := by
        simp only [totalD, haligned]
        rw [Finset.sum_comm]
      _ ≤ ∑ r : R, capacity r :=
        Finset.sum_le_sum fun r _ => hcolumn r
      _ = C := rfl
  have hpair (r q : R) :
      (∑ i : I, cross i r * cross i q) ≤
        min (capacity r) (capacity q) := by
    exact pairLoad_le_minColumnCapacity
      (fun i => cross i r) (fun i => cross i q)
      (capacity r) (capacity q)
      (fun i => hcross i r) (fun i => hcross i q)
      (hcolumn r) (hcolumn q)
  have hsquare : totalDsq ≤ Q := by
    calc
      totalDsq = ∑ i : I, ∑ r : R, ∑ q : R,
          cross i r * cross i q := by
        dsimp [totalDsq]
        simp_rw [haligned, pow_two, Finset.sum_mul, Finset.mul_sum]
      _ = ∑ r : R, ∑ q : R, ∑ i : I,
          cross i r * cross i q := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.sum_comm]
      _ ≤ ∑ r : R, ∑ q : R, min (capacity r) (capacity q) := by
        exact Finset.sum_le_sum fun r _ =>
          Finset.sum_le_sum fun q _ => hpair r q
      _ = Q := rfl
  have hcard : 4 * Fintype.card I ≤ totalD := by
    have hsum := Finset.sum_le_sum
      (s := (Finset.univ : Finset I)) (f := fun _ : I => 4) (g := D)
      (fun i _ => hlegal i)
    simpa [totalD, Nat.mul_comm] using hsum
  have hcostIdentity :
      4 * (∑ i : I, (D i + 1) ^ 2) =
        4 * totalDsq + 8 * totalD + 4 * Fintype.card I := by
    calc
      4 * (∑ i : I, (D i + 1) ^ 2) =
          ∑ i : I, 4 * (D i + 1) ^ 2 := by rw [Finset.mul_sum]
      _ = ∑ i : I, (4 * (D i) ^ 2 + 8 * D i + 4) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 4 * totalDsq + 8 * totalD + 4 * Fintype.card I := by
        simp [totalDsq, totalD, Finset.sum_add_distrib,
          Finset.mul_sum, Nat.mul_comm]
  have hscaled : 4 * (∑ i : I, (D i + 1) ^ 2) ≤ 4 * Q + 9 * C := by
    rw [hcostIdentity]
    nlinarith
  have henv : 4 * Q + 9 * C ≤ 4 * rlBudget s d := by
    simpa [Q, C] using henvelope
  have hfour := hscaled.trans henv
  omega

/-- Aggregate arithmetic for the first two rows below the double-slack
boundary.  In a layer profile one takes

* `A = sum x_r*x_(r+1)`,
* `B = sum x_r*(x_r-1)`,
* `C = sum c_r`, and
* `Q = sum_{r,q} min(c_r,c_q)`.

The three displayed hypotheses are the exact finite-profile estimates.  This
theorem performs only their final polynomial comparison with the RL budget;
it does not assert those estimates for an arbitrary graph. -/
theorem nearBoundaryEnvelope_of_profileAggregates
    (s d Q C A B : ℕ) (hs : 4 ≤ s)
    (hrow : d = 2 * s - 1 ∨ d = 2 * s - 2)
    (hquadratic : Q + 2 * B + A ≤ 4 * s ^ 2)
    (hlinear : C = 2 * s + A)
    (htrade : 5 * A ≤ 8 * B + 5 * (s - 1)) :
    4 * Q + 9 * C ≤ 4 * rlBudget s d := by
  have hquad4 : 4 * Q + 8 * B + 4 * A ≤ 16 * s ^ 2 := by
    nlinarith
  have hcore : 4 * Q + 9 * A ≤ 16 * s ^ 2 + 5 * s := by
    have hpred : s - 1 + 1 = s := by omega
    omega
  have hprofile : 4 * Q + 9 * C ≤ 16 * s ^ 2 + 23 * s := by
    rw [hlinear]
    nlinarith
  have hbudget : rlBudget s d = 5 * s ^ 2 + 2 * s := by
    rcases hrow with hrow | hrow
    · subst d
      let t := s - 1
      have hsEq : s = t + 1 := by simp [t]; omega
      rw [hsEq]
      have ht : 3 ≤ t := by omega
      have hd : 2 * (t + 1) - 1 = 2 * t + 1 := by omega
      rw [hd]
      have hp : partnerDistance (2 * t + 1) = 1 := by
        simp [partnerDistance]
        omega
      unfold rlBudget
      rw [hp]
      ring
    · subst d
      let t := s - 1
      have hsEq : s = t + 1 := by simp [t]; omega
      rw [hsEq]
      have ht : 3 ≤ t := by omega
      have hd : 2 * (t + 1) - 2 = 2 * t := by omega
      rw [hd]
      have hp : partnerDistance (2 * t) = 2 := by
        simp [partnerDistance]
      unfold rlBudget
      rw [hp]
      ring
  rw [hbudget]
  have hfactor : 15 ≤ 4 * s := by omega
  have hpoly : 15 * s ≤ 4 * s ^ 2 := by
    simpa [pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.mul_le_mul_right s hfactor
  exact hprofile.trans (by omega)

/-- A simpler near-boundary landing used when the structural classification
directly bounds total residual capacity by `2s+2`.  The universal pair-minimum
term then needs only the coarse square bound `Q<=4s^2`. -/
theorem nearBoundaryEnvelope_of_quadratic_and_linearBounds
    (s d Q C : ℕ) (hs : 4 ≤ s)
    (hrow : d = 2 * s - 1 ∨ d = 2 * s - 2)
    (hquadratic : Q ≤ 4 * s ^ 2)
    (hlinear : C ≤ 2 * s + 2) :
    4 * Q + 9 * C ≤ 4 * rlBudget s d := by
  have hprofile : 4 * Q + 9 * C ≤ 16 * s ^ 2 + 18 * s + 18 := by
    nlinarith
  have hbudget : rlBudget s d = 5 * s ^ 2 + 2 * s := by
    rcases hrow with hrow | hrow
    · subst d
      let t := s - 1
      have hsEq : s = t + 1 := by simp [t]; omega
      rw [hsEq]
      have ht : 3 ≤ t := by omega
      have hd : 2 * (t + 1) - 1 = 2 * t + 1 := by omega
      rw [hd]
      have hp : partnerDistance (2 * t + 1) = 1 := by
        simp [partnerDistance]
        omega
      unfold rlBudget
      rw [hp]
      ring
    · subst d
      let t := s - 1
      have hsEq : s = t + 1 := by simp [t]; omega
      rw [hsEq]
      have ht : 3 ≤ t := by omega
      have hd : 2 * (t + 1) - 2 = 2 * t := by omega
      rw [hd]
      have hp : partnerDistance (2 * t) = 2 := by
        simp [partnerDistance]
      unfold rlBudget
      rw [hp]
      ring
  rw [hbudget]
  have hfactor : 10 * s + 18 ≤ 4 * s ^ 2 := by
    nlinarith [sq_nonneg (2 * s - 3)]
  omega

/-- Threshold-cut graph wrapper for the arbitrary-capacity matrix theorem.
The cut-capacity premise is literal and RFC supplies the residual column
bound after the root-stub demand consumes one crossing edge. -/
theorem totalCost_le_rlBudget_of_levelAlignedCutCapacities
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (w x₀ : V) (m₁ m₂ : I → V) (level : V → ℕ)
    (s d : ℕ) (capacity : Fin d → ℕ)
    (hroot : level w = 0) (hstub : level x₀ = d)
    (hendpoint₁ : ∀ i, level (m₁ i) ≤ d)
    (hendpoint₂ : ∀ i, level (m₂ i) ≤ d)
    (haligned : ∀ i,
      G.dist (m₁ i) (m₂ i) = Nat.dist (level (m₁ i)) (level (m₂ i)))
    (hRFC : ∀ T : Finset V, w ∉ T →
      (∑ i : I, separationDemand T (m₁ i) (m₂ i)) +
        (if x₀ ∈ T then 1 else 0) ≤ cutSize G T)
    (hcut : ∀ r : Fin d,
      cutSize G (levelUpperCut level r.1) ≤ capacity r + 1)
    (hlegal : ∀ i, 4 ≤ G.dist (m₁ i) (m₂ i))
    (henvelope :
      4 * (∑ r : Fin d, ∑ q : Fin d,
          min (capacity r) (capacity q)) +
          9 * (∑ r : Fin d, capacity r) ≤
        4 * rlBudget s d) :
    (∑ i : I, (G.dist (m₁ i) (m₂ i) + 1) ^ 2) ≤ rlBudget s d := by
  classical
  let cross : I → Fin d → ℕ := fun i r =>
    separationDemand (levelUpperCut level r.1) (m₁ i) (m₂ i)
  have hsep (r : Fin d) (a b : V) :
      separationDemand (levelUpperCut level r.1) a b =
        separation (decide (r.1 < level a)) (decide (r.1 < level b)) := by
    simp [separationDemand, separation]
    by_cases ha : r.1 < level a <;> by_cases hb : r.1 < level b <;>
      simp [ha, hb]
  have hcross : ∀ i r, cross i r ≤ 1 := by
    intro i r
    rw [show cross i r = separation
      (decide (r.1 < level (m₁ i)))
      (decide (r.1 < level (m₂ i))) by exact hsep r _ _]
    cases decide (r.1 < level (m₁ i)) <;>
      cases decide (r.1 < level (m₂ i)) <;> simp [separation]
  have hmatrixAligned : ∀ i,
      G.dist (m₁ i) (m₂ i) = ∑ r : Fin d, cross i r := by
    intro i
    rw [haligned i]
    rw [show (∑ r : Fin d, cross i r) =
        ∑ r : Fin d, separation
          (decide (r.1 < level (m₁ i)))
          (decide (r.1 < level (m₂ i))) by
      apply Finset.sum_congr rfl
      intro r _
      exact hsep r _ _]
    rw [show (∑ r : Fin d, separation
        (decide (r.1 < level (m₁ i)))
        (decide (r.1 < level (m₂ i)))) =
        ∑ k ∈ Finset.range d, separation
          (decide (k < level (m₁ i)))
          (decide (k < level (m₂ i))) by
      simpa using Fin.sum_univ_eq_sum_range
        (fun k => separation
          (decide (k < level (m₁ i)))
          (decide (k < level (m₂ i)))) d]
    exact (sum_thresholdSeparation_eq_dist
      (hendpoint₁ i) (hendpoint₂ i)).symm
  have hcolumn : ∀ r : Fin d,
      (∑ i : I, cross i r) ≤ capacity r := by
    intro r
    have hw : w ∉ levelUpperCut level r.1 := by simp [hroot]
    have hx : x₀ ∈ levelUpperCut level r.1 := by simp [hstub, r.2]
    have hvalid := hRFC (levelUpperCut level r.1) hw
    simp only [hx, if_true] at hvalid
    exact Nat.le_of_add_le_add_right (hvalid.trans (hcut r))
  exact totalCost_le_rlBudget_of_minColumnEnvelope
    (fun i => G.dist (m₁ i) (m₂ i)) cross capacity s d
    hcross hmatrixAligned hcolumn hlegal henvelope

/-- Near-boundary graph wrapper.  A structural argument now needs only a
profile weight of total at most `2s`, a pointwise square bound on residual
cut capacity, and total residual capacity at most `2s+2`. -/
theorem totalCost_le_rlBudget_of_nearBoundaryCapacityProfile
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (w x₀ : V) (m₁ m₂ : I → V) (level : V → ℕ)
    (s d : ℕ) (capacity weight : Fin d → ℕ)
    (hs : 4 ≤ s) (hrow : d = 2 * s - 1 ∨ d = 2 * s - 2)
    (hcapacity : ∀ r, capacity r ≤ (weight r) ^ 2)
    (hweight : (∑ r : Fin d, weight r) ≤ 2 * s)
    (hcapacitySum : (∑ r : Fin d, capacity r) ≤ 2 * s + 2)
    (hroot : level w = 0) (hstub : level x₀ = d)
    (hendpoint₁ : ∀ i, level (m₁ i) ≤ d)
    (hendpoint₂ : ∀ i, level (m₂ i) ≤ d)
    (haligned : ∀ i,
      G.dist (m₁ i) (m₂ i) = Nat.dist (level (m₁ i)) (level (m₂ i)))
    (hRFC : ∀ T : Finset V, w ∉ T →
      (∑ i : I, separationDemand T (m₁ i) (m₂ i)) +
        (if x₀ ∈ T then 1 else 0) ≤ cutSize G T)
    (hcut : ∀ r : Fin d,
      cutSize G (levelUpperCut level r.1) ≤ capacity r + 1)
    (hlegal : ∀ i, 4 ≤ G.dist (m₁ i) (m₂ i)) :
    (∑ i : I, (G.dist (m₁ i) (m₂ i) + 1) ^ 2) ≤ rlBudget s d := by
  have hQ := minColumnEnvelope_le_four_sq capacity weight s hcapacity hweight
  have henv := nearBoundaryEnvelope_of_quadratic_and_linearBounds
    s d
    (∑ r : Fin d, ∑ q : Fin d, min (capacity r) (capacity q))
    (∑ r : Fin d, capacity r)
    hs hrow hQ hcapacitySum
  exact totalCost_le_rlBudget_of_levelAlignedCutCapacities
    w x₀ m₁ m₂ level s d capacity hroot hstub
    hendpoint₁ hendpoint₂ haligned hRFC hcut hlegal henv

#print axioms pairLoad_le_minColumnCapacity
#print axioms adjacentExtraCapacity_le_sum_sq
#print axioms minColumnEnvelope_le_four_sq
#print axioms totalCost_le_rlBudget_of_minColumnEnvelope
#print axioms nearBoundaryEnvelope_of_profileAggregates
#print axioms nearBoundaryEnvelope_of_quadratic_and_linearBounds
#print axioms totalCost_le_rlBudget_of_levelAlignedCutCapacities
#print axioms totalCost_le_rlBudget_of_nearBoundaryCapacityProfile

end Erdos23GapGBLayerCapacity
