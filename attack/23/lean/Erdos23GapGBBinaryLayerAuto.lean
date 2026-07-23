/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair, OpenAI Codex
-/
import ErdosProblems.Erdos23GapGBBinaryLayers

/-!
# Erdős 23 G-B: automatic profiles for binary level layers

This module removes bookkeeping hypotheses from the binary-layer theorem.
If level `k` contains `1 + extra k` vertices, where `extra k` is zero or
one, then the adjacent-layer product has the canonical profile

`1 + active + 2 * high`,

where `active` records that at least one endpoint layer is doubled and
`high` records that both are doubled.  The identity

`active(r) + high(r) = extra(r) + extra(r+1)`

also proves the global profile bound from the number of extra vertices.
The only remaining scalar profile input is the sharp run bound
`sum high + 1 <= s`; in applications it records the number of adjacent
pairs of doubled levels.
-/

namespace Erdos23GapGBBinaryLayerAuto

open scoped BigOperators
open SimpleGraph
open Erdos23GapGA
open Erdos23GapGBSeries
open Erdos23GapGBBinaryLayers

/-- The zero-one indicator that at least one endpoint of a level gap is
doubled, written arithmetically. -/
def binaryActive (extra : ℕ → ℕ) (r : ℕ) : ℕ :=
  extra r + extra (r + 1) - extra r * extra (r + 1)

/-- The zero-one indicator that both endpoint levels of a gap are doubled. -/
def binaryHigh (extra : ℕ → ℕ) (r : ℕ) : ℕ :=
  extra r * extra (r + 1)

/-- Truth-table identity for the canonical binary gap profile. -/
theorem binaryActive_add_binaryHigh
    (extra : ℕ → ℕ) (r : ℕ)
    (hleft : extra r ≤ 1) (hright : extra (r + 1) ≤ 1) :
    binaryActive extra r + binaryHigh extra r =
      extra r + extra (r + 1) := by
  unfold binaryActive binaryHigh
  interval_cases extra r <;> interval_cases extra (r + 1) <;> simp

/-- A canonical active indicator is zero or one. -/
theorem binaryActive_le_one
    (extra : ℕ → ℕ) (r : ℕ)
    (hleft : extra r ≤ 1) (hright : extra (r + 1) ≤ 1) :
    binaryActive extra r ≤ 1 := by
  unfold binaryActive
  interval_cases extra r <;> interval_cases extra (r + 1) <;> simp

/-- A high gap is necessarily active. -/
theorem binaryHigh_le_binaryActive
    (extra : ℕ → ℕ) (r : ℕ)
    (hleft : extra r ≤ 1) (hright : extra (r + 1) ≤ 1) :
    binaryHigh extra r ≤ binaryActive extra r := by
  unfold binaryActive binaryHigh
  interval_cases extra r <;> interval_cases extra (r + 1) <;> simp

/-- The product of two binary layer sizes has the canonical profile. -/
theorem binaryLayerProduct_eq_profile
    (extra : ℕ → ℕ) (r : ℕ)
    (hleft : extra r ≤ 1) (hright : extra (r + 1) ≤ 1) :
    (extra r + 1) * (extra (r + 1) + 1) =
      binaryActive extra r + 2 * binaryHigh extra r + 1 := by
  unfold binaryActive binaryHigh
  interval_cases extra r <;> interval_cases extra (r + 1) <;> simp

/-- Shifting a finite natural sum by one only discards its first term. -/
theorem sum_range_shift_add_head (f : ℕ → ℕ) (d : ℕ) :
    (∑ r ∈ Finset.range d, f (r + 1)) + f 0 =
      ∑ k ∈ Finset.range (d + 1), f k := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      omega

/-- Every gap counts two endpoint extras, while every level extra is counted
at most twice. -/
theorem sum_adjacentExtras_le_twice_sum
    (extra : ℕ → ℕ) (d : ℕ) :
    (∑ r ∈ Finset.range d, (extra r + extra (r + 1))) ≤
      2 * ∑ k ∈ Finset.range (d + 1), extra k := by
  have hleft : (∑ r ∈ Finset.range d, extra r) ≤
      ∑ k ∈ Finset.range (d + 1), extra k := by
    rw [Finset.sum_range_succ]
    omega
  have hright : (∑ r ∈ Finset.range d, extra (r + 1)) ≤
      ∑ k ∈ Finset.range (d + 1), extra k := by
    have hshift := sum_range_shift_add_head extra d
    omega
  rw [Finset.sum_add_distrib]
  omega

/-- The active-plus-high profile count is at most twice the number of
doubled levels. -/
theorem sum_binaryProfile_le_twice_sum
    (extra : ℕ → ℕ) (d : ℕ)
    (hbinary : ∀ k < d + 1, extra k ≤ 1) :
    (∑ r ∈ Finset.range d, binaryActive extra r) +
        (∑ r ∈ Finset.range d, binaryHigh extra r) ≤
      2 * ∑ k ∈ Finset.range (d + 1), extra k := by
  rw [← Finset.sum_add_distrib]
  calc
    (∑ r ∈ Finset.range d,
        (binaryActive extra r + binaryHigh extra r)) =
        ∑ r ∈ Finset.range d, (extra r + extra (r + 1)) := by
          apply Finset.sum_congr rfl
          intro r hr
          have hrlt : r < d := Finset.mem_range.mp hr
          exact binaryActive_add_binaryHigh extra r
            (hbinary r (by omega)) (hbinary (r + 1) (by omega))
    _ ≤ 2 * ∑ k ∈ Finset.range (d + 1), extra k :=
      sum_adjacentExtras_le_twice_sum extra d

/-- Graph-facing automatic binary-layer wrapper.

The function `extra` literally records the number of vertices beyond the
one corridor vertex on each level.  All structural graph content remains
visible: adjacent edges change level by one, legal demand pairs are level
aligned, and the exact layer-cardinality identity is supplied explicitly.
-/
theorem totalCost_le_rlBudget_of_binaryLayerExtras_levelAligned
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (w x₀ : V) (m₁ m₂ : I → V) (level : V → ℕ)
    (s d : ℕ) (extra : Fin (d + 1) → ℕ)
    (hstep : ∀ {u v : V}, G.Adj u v →
      Nat.dist (level u) (level v) = 1)
    (hlayer : ∀ k : Fin (d + 1),
      (levelLayer level k.1).card = extra k + 1)
    (hbinary : ∀ k, extra k ≤ 1)
    (hextra : (∑ k : Fin (d + 1), extra k) ≤ s)
    (hhighBudget :
      (∑ r : Fin d,
        binaryHigh (fun k => if hk : k < d + 1 then extra ⟨k, hk⟩ else 0) r.1) + 1 ≤ s)
    (hroot : level w = 0) (hstub : level x₀ = d)
    (hendpoint₁ : ∀ i, level (m₁ i) ≤ d)
    (hendpoint₂ : ∀ i, level (m₂ i) ≤ d)
    (haligned : ∀ i,
      G.dist (m₁ i) (m₂ i) = Nat.dist (level (m₁ i)) (level (m₂ i)))
    (hRFC : ∀ T : Finset V, w ∉ T →
      (∑ i : I, separationDemand T (m₁ i) (m₂ i)) +
        (if x₀ ∈ T then 1 else 0) ≤ cutSize G T)
    (hlegal : ∀ i, 4 ≤ G.dist (m₁ i) (m₂ i)) :
    (∑ i : I, (G.dist (m₁ i) (m₂ i) + 1) ^ 2) ≤ rlBudget s d := by
  classical
  let e : ℕ → ℕ := fun k => if hk : k < d + 1 then extra ⟨k, hk⟩ else 0
  let active : Fin d → ℕ := fun r => binaryActive e r.1
  let high : Fin d → ℕ := fun r => binaryHigh e r.1
  have he_fin (k : Fin (d + 1)) : e k.1 = extra k := by
    rw [show e k.1 = extra ⟨k.1, k.2⟩ by
      simp only [e, dif_pos k.2]]
  have he_binary : ∀ k < d + 1, e k ≤ 1 := by
    intro k hk
    rw [show e k = extra ⟨k, hk⟩ by
      simp only [e, dif_pos hk]]
    exact hbinary ⟨k, hk⟩
  have hpairProfile : ∀ r : Fin d,
      (levelLayer level r.1).card *
          (levelLayer level (r.1 + 1)).card =
        active r + 2 * high r + 1 := by
    intro r
    have hr0 : r.1 < d + 1 := by omega
    have hr1 : r.1 + 1 < d + 1 := by omega
    rw [hlayer ⟨r.1, hr0⟩, hlayer ⟨r.1 + 1, hr1⟩]
    rw [← he_fin ⟨r.1, hr0⟩, ← he_fin ⟨r.1 + 1, hr1⟩]
    exact binaryLayerProduct_eq_profile e r.1
      (he_binary r.1 hr0) (he_binary (r.1 + 1) hr1)
  have hactive : ∀ r, active r ≤ 1 := by
    intro r
    exact binaryActive_le_one e r.1
      (he_binary r.1 (by omega)) (he_binary (r.1 + 1) (by omega))
  have hhigh : ∀ r, high r ≤ active r := by
    intro r
    exact binaryHigh_le_binaryActive e r.1
      (he_binary r.1 (by omega)) (he_binary (r.1 + 1) (by omega))
  have hHL : (∑ r : Fin d, high r) ≤ ∑ r : Fin d, active r := by
    exact Finset.sum_le_sum fun r _ => hhigh r
  have hprofileRange :
      (∑ r ∈ Finset.range d, binaryActive e r) +
          (∑ r ∈ Finset.range d, binaryHigh e r) ≤
        2 * ∑ k ∈ Finset.range (d + 1), e k :=
    sum_binaryProfile_le_twice_sum e d he_binary
  have hsumExtra : (∑ k ∈ Finset.range (d + 1), e k) =
      ∑ k : Fin (d + 1), extra k := by
    rw [show (∑ k : Fin (d + 1), extra k) =
        ∑ k : Fin (d + 1), e k.1 by
      apply Finset.sum_congr rfl
      intro k _
      exact (he_fin k).symm]
    simpa using (Fin.sum_univ_eq_sum_range e (d + 1)).symm
  have hLH : (∑ r : Fin d, active r) + (∑ r : Fin d, high r) ≤ 2 * s := by
    have hactiveRange : (∑ r : Fin d, active r) =
        ∑ r ∈ Finset.range d, binaryActive e r := by
      simpa [active] using Fin.sum_univ_eq_sum_range (binaryActive e) d
    have hhighRange : (∑ r : Fin d, high r) =
        ∑ r ∈ Finset.range d, binaryHigh e r := by
      simpa [high] using Fin.sum_univ_eq_sum_range (binaryHigh e) d
    rw [hactiveRange, hhighRange]
    rw [hsumExtra] at hprofileRange
    exact hprofileRange.trans (Nat.mul_le_mul_left 2 hextra)
  have hHs : (∑ r : Fin d, high r) + 1 ≤ s := by
    simpa [high, e] using hhighBudget
  exact totalCost_le_rlBudget_of_binaryBfsLayers_levelAligned
    w x₀ m₁ m₂ level s d active high hstep hpairProfile
    hroot hstub hendpoint₁ hendpoint₂ haligned hRFC
    hactive hhigh hlegal hHL hLH hHs

#print axioms binaryActive_add_binaryHigh
#print axioms sum_binaryProfile_le_twice_sum
#print axioms totalCost_le_rlBudget_of_binaryLayerExtras_levelAligned

end Erdos23GapGBBinaryLayerAuto
