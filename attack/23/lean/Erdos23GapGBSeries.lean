/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair, OpenAI Codex
-/
import Mathlib

/-!
# Erdős 23 gap G-B: series composition across a corridor bridge

This file isolates a proper inductive reduction for the remaining multi-edge
rooted lemma RL*.  Join two disjoint one-stub rooted blocks by one cut-graph
edge from the first stub terminal to the second root terminal.  At every cut,
the new global stub demand is dominated by the two old stub demands plus the
new bridge edge.  The exact RL budget is superadditive under the corresponding
parameter law

`s = s₁+s₂`, `d = d₁+d₂+1`.

Consequently a counterexample cannot contain a corridor bridge with two
already-controlled rooted blocks on its sides.  Under the Gamma induction,
both blocks are controlled whenever both bridge components have at least four
vertices, because the minimal composite for a block adds at most three
vertices.  This reduction asks only for an interior corridor bridge; it does
not assume that the whole cut graph is 2-connected.
-/

namespace Erdos23GapGBSeries

/-- The parity-minimal admissible partner distance from the RL statement.
Only positive stub distances are used by the graph application. -/
def partnerDistance (d : ℕ) : ℕ :=
  if d = 1 then 3 else if d % 2 = 0 then 2 else 1

@[simp]
theorem partnerDistance_one : partnerDistance 1 = 3 := by
  simp [partnerDistance]

theorem partnerDistance_pos (d : ℕ) : 1 ≤ partnerDistance d := by
  by_cases h1 : d = 1
  · simp [partnerDistance, h1]
  · by_cases heven : d % 2 = 0 <;> simp [partnerDistance, h1, heven]

theorem partnerDistance_le_three (d : ℕ) : partnerDistance d ≤ 3 := by
  by_cases h1 : d = 1
  · simp [partnerDistance, h1]
  · by_cases heven : d % 2 = 0 <;> simp [partnerDistance, h1, heven]

/-- The exact right-hand side of rooted lemma RL, parameterized by corridor
slack `s` and stub distance `d`. -/
def rlBudget (s d : ℕ) : ℕ :=
  s * (2 * d + 2 + s) + 2 * s * partnerDistance d

/-- Membership-bit separation, i.e. the contribution of one edge or one
unit terminal demand to a cut. -/
def separation (a b : Bool) : ℕ :=
  if a = b then 0 else 1

/-- Rooted cut validity is independent of which terminal is named as the
root once written in symmetric separation form. -/
theorem separation_comm (a b : Bool) : separation a b = separation b a := by
  cases a <;> cases b <;> simp [separation]

theorem rootedCutCondition_swapTerminals
    {b m : ℕ} {w x : Bool} (h : m + separation w x ≤ b) :
    m + separation x w ≤ b := by
  rw [separation_comm]
  exact h

/-- A terminal separated from the far endpoint of a three-link chain must be
separated across at least one link of that chain.  This is the exact cutwise
reason that series composition preserves rooted validity. -/
theorem separation_le_series (w₁ x₁ w₂ x₂ : Bool) :
    separation w₁ x₂ ≤
      separation w₁ x₁ + separation x₁ w₂ + separation w₂ x₂ := by
  cases w₁ <;> cases x₁ <;> cases w₂ <;> cases x₂ <;>
    simp [separation]

/-- Cutwise rooted-validity composition.

`bᵢ` and `mᵢ` are respectively the B-cut and internal-M-cut counts in
block `i`.  The bridge contribution is `separation x₁ w₂`; the global
stub terminals are `w₁,x₂`.  Thus the theorem can be instantiated at
every vertex cut, with no routing or two-connectedness assumption. -/
theorem rootedCutCondition_series
    {b₁ m₁ b₂ m₂ : ℕ} {w₁ x₁ w₂ x₂ : Bool}
    (h₁ : m₁ + separation w₁ x₁ ≤ b₁)
    (h₂ : m₂ + separation w₂ x₂ ≤ b₂) :
    m₁ + m₂ + separation w₁ x₂ ≤
      b₁ + b₂ + separation x₁ w₂ := by
  have hsep := separation_le_series w₁ x₁ w₂ x₂
  omega

/-- Universally quantified cut-family form of
`rootedCutCondition_series`.  An application takes `ι` to be the finite
vertex subsets and supplies the four terminal-membership bits of each cut. -/
theorem rootedCutCondition_series_family
    {ι : Type*} (b₁ m₁ b₂ m₂ : ι → ℕ)
    (w₁ x₁ w₂ x₂ : ι → Bool)
    (h₁ : ∀ T, m₁ T + separation (w₁ T) (x₁ T) ≤ b₁ T)
    (h₂ : ∀ T, m₂ T + separation (w₂ T) (x₂ T) ≤ b₂ T) :
    ∀ T, m₁ T + m₂ T + separation (w₁ T) (x₂ T) ≤
      b₁ T + b₂ T + separation (x₁ T) (w₂ T) := by
  intro T
  exact rootedCutCondition_series (h₁ T) (h₂ T)

/-- Exact slack accounting for two disjoint blocks joined by one bridge.
The hypotheses say that each stub geodesic fits inside its block. -/
theorem series_slack_identity
    {n₁ n₂ d₁ d₂ : ℕ} (h₁ : d₁ + 1 ≤ n₁) (h₂ : d₂ + 1 ≤ n₂) :
    n₁ + n₂ - 1 - (d₁ + d₂ + 1) =
      (n₁ - 1 - d₁) + (n₂ - 1 - d₂) := by
  omega

/-- The exact RL budget is superadditive under series composition. -/
theorem rlBudget_series_superadditive
    {s₁ s₂ d₁ d₂ : ℕ} (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂) :
    rlBudget s₁ d₁ + rlBudget s₂ d₂ ≤
      rlBudget (s₁ + s₂) (d₁ + d₂ + 1) := by
  have hp₁ := partnerDistance_le_three d₁
  have hp₂ := partnerDistance_le_three d₂
  have hp := partnerDistance_pos (d₁ + d₂ + 1)
  have hcross₁ : partnerDistance d₁ ≤
      d₂ + 1 + partnerDistance (d₁ + d₂ + 1) := by
    omega
  have hcross₂ : partnerDistance d₂ ≤
      d₁ + 1 + partnerDistance (d₁ + d₂ + 1) := by
    omega
  have hmul₁ := Nat.mul_le_mul_left (2 * s₁) hcross₁
  have hmul₂ := Nat.mul_le_mul_left (2 * s₂) hcross₂
  unfold rlBudget
  nlinarith

/-- If each side satisfies its rooted RL estimate, then their disjoint
series composite satisfies RL as well.  Gamma is additive because the
bridge is the only inter-block B-edge and there are no inter-block M-edges;
the graph application supplies that exact identity. -/
theorem gamma_series_le_rlBudget
    {s₁ s₂ d₁ d₂ Γ₁ Γ₂ : ℕ}
    (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂)
    (hΓ₁ : Γ₁ ≤ rlBudget s₁ d₁)
    (hΓ₂ : Γ₂ ≤ rlBudget s₂ d₂) :
    Γ₁ + Γ₂ ≤ rlBudget (s₁ + s₂) (d₁ + d₂ + 1) := by
  exact (Nat.add_le_add hΓ₁ hΓ₂).trans
    (rlBudget_series_superadditive hd₁ hd₂)

/-- The minimal composite attached to either block has fewer vertices than
the whole series composite as soon as the opposite bridge component has at
least four vertices.  This is the exact size gate needed to invoke strict
Gamma induction. -/
theorem minimalComposite_sizes_lt_series_of_partner_lt
    {n₁ n₂ d₁ d₂ : ℕ}
    (hp₁ : partnerDistance d₁ < n₂)
    (hp₂ : partnerDistance d₂ < n₁) :
    n₁ + partnerDistance d₁ < n₁ + n₂ ∧
      n₂ + partnerDistance d₂ < n₁ + n₂ := by
  omega

/-- Exact characterization of the strict induction-size gate.  Unlike the
old uniform `4 <= n_i` wrapper, this retains the actual partner distances
and therefore applies to many two- and three-vertex endpoint blocks. -/
theorem minimalComposite_sizes_lt_series_iff
    {n₁ n₂ d₁ d₂ : ℕ} :
    (n₁ + partnerDistance d₁ < n₁ + n₂ ∧
      n₂ + partnerDistance d₂ < n₁ + n₂) ↔
      partnerDistance d₁ < n₂ ∧ partnerDistance d₂ < n₁ := by
  omega

theorem minimalComposite_sizes_lt_series
    {n₁ n₂ d₁ d₂ : ℕ} (hn₁ : 4 ≤ n₁) (hn₂ : 4 ≤ n₂) :
    n₁ + partnerDistance d₁ < n₁ + n₂ ∧
      n₂ + partnerDistance d₂ < n₁ + n₂ := by
  have hp₁ := partnerDistance_le_three d₁
  have hp₂ := partnerDistance_le_three d₂
  exact minimalComposite_sizes_lt_series_of_partner_lt (by omega) (by omega)

end Erdos23GapGBSeries
