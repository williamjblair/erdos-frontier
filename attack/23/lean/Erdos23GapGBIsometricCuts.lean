/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair, OpenAI Codex
-/
import ErdosProblems.Erdos23GapGBEqualityBoundary

/-!
# Erdős 23 G-B: isometric size-two cut bases

An even cycle has a canonical family of opposite-edge cuts whose separation
count equals graph distance.  A linear chain of even cycles inherits the
union of those cut coordinates.  Every such cut has supply capacity two and
separates the rooted terminals, so RFC leaves capacity one for all internal
demands together.

This module proves the graph-independent landing for that strategy.  It does
not assert that an arbitrary BF-RL instance has such a cut basis; the intended
application is the canonical pure-mass interval geometry.
-/

namespace Erdos23GapGBIsometricCuts

open scoped BigOperators
open SimpleGraph
open Erdos23GapGA
open Erdos23GapGBSeries
open Erdos23GapGBEqualityBoundary

/-- Sharp convexity for a finite family of at least two legal distances.
After writing `D_i=E_i+4`, the elementary inequality
`sum E_i^2 <= (sum E_i)^2` shows that concentrating all excess over four on
one demand is worst. -/
theorem sum_add_one_sq_le_total_sub_three_sq_add_twentyFive
    {I : Type*} [Fintype I] (D : I → ℕ)
    (hcard : 2 ≤ Fintype.card I)
    (hlegal : ∀ i, 4 ≤ D i) :
    (∑ i : I, (D i + 1) ^ 2) ≤
      ((∑ i : I, D i) - 3) ^ 2 + 25 := by
  classical
  let E : I → ℕ := fun i => D i - 4
  let totalE := ∑ i : I, E i
  let count := Fintype.card I
  have hDE (i : I) : D i = E i + 4 := by
    simp only [E]
    have hi := hlegal i
    omega
  have htotal : (∑ i : I, D i) = totalE + 4 * count := by
    simp_rw [hDE]
    simp [totalE, count, Finset.sum_add_distrib, Nat.mul_comm]
  have hsquares : (∑ i : I, (E i) ^ 2) ≤ totalE ^ 2 := by
    exact Finset.sum_sq_le_sq_sum_of_nonneg
      (s := (Finset.univ : Finset I)) (f := E)
      (fun _ _ => Nat.zero_le _)
  have hcost : (∑ i : I, (D i + 1) ^ 2) =
      (∑ i : I, (E i) ^ 2) + 10 * totalE + 25 * count := by
    simp_rw [hDE]
    calc
      (∑ i : I, (E i + 4 + 1) ^ 2) =
          ∑ i : I, ((E i) ^ 2 + 10 * E i + 25) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i : I, (E i) ^ 2) + 10 * totalE + 25 * count := by
        simp [totalE, count, Finset.sum_add_distrib, Finset.mul_sum,
          Nat.mul_comm]
  let k := count - 2
  have hcountEq : count = k + 2 := by simp [k]; omega
  have hsub : totalE + 4 * (k + 2) - 3 = totalE + 4 * k + 5 := by omega
  rw [hcost, htotal, hcountEq, hsub]
  nlinarith

/-- Two or more legal demands whose total distance is at most the corridor
length fit the RL budget throughout `d <= 2s`. -/
theorem totalCost_le_rlBudget_of_sumDistances_le_length
    {I : Type*} [Fintype I] (D : I → ℕ) (s d : ℕ)
    (hcard : 2 ≤ Fintype.card I)
    (hlegal : ∀ i, 4 ≤ D i)
    (hsum : (∑ i : I, D i) ≤ d)
    (hds : d ≤ 2 * s) :
    (∑ i : I, (D i + 1) ^ 2) ≤ rlBudget s d := by
  classical
  let totalD := ∑ i : I, D i
  let count := Fintype.card I
  have hcount : 4 * count ≤ totalD := by
    have h := Finset.sum_le_sum
      (s := (Finset.univ : Finset I))
      (f := fun _ : I => 4) (g := D) (fun i _ => hlegal i)
    simpa [totalD, count, Nat.mul_comm] using h
  have hother (i : I) : 4 ≤ ∑ j ∈ (Finset.univ : Finset I).erase i, D j := by
    obtain ⟨j, hji⟩ : ∃ j : I, j ≠ i := by
      by_contra hnone
      push Not at hnone
      have hsub : (Finset.univ : Finset I) ⊆ {i} := by
        intro x _
        simp [hnone x]
      have hcardLe : Fintype.card I ≤ 1 := by
        simpa using Finset.card_le_card hsub
      omega
    have hjmem : j ∈ (Finset.univ : Finset I).erase i := by simp [hji]
    calc
      4 ≤ D j := hlegal j
      _ ≤ ∑ k ∈ (Finset.univ : Finset I).erase i, D k := by
        exact Finset.single_le_sum
          (fun k _ => Nat.zero_le (D k)) hjmem
  have hroom (i : I) : D i + 4 ≤ d := by
    have hsplit := Finset.sum_erase_add
      (Finset.univ : Finset I) D (Finset.mem_univ i)
    have hrest := hother i
    have htot : totalD ≤ d := hsum
    simp only [totalD] at htot
    omega
  have hpoint (i : I) :
      (D i + 1) ^ 2 ≤ (d - 3) * (D i + 1) := by
    have hbound : D i + 1 ≤ d - 3 := by
      have := hroom i
      omega
    simpa [pow_two] using Nat.mul_le_mul_right (D i + 1) hbound
  have hcostLinear :
      (∑ i : I, (D i + 1) ^ 2) ≤
        (d - 3) * (totalD + count) := by
    calc
      (∑ i : I, (D i + 1) ^ 2) ≤
          ∑ i : I, (d - 3) * (D i + 1) :=
        Finset.sum_le_sum fun i _ => hpoint i
      _ = (d - 3) * (totalD + count) := by
        rw [← Finset.mul_sum]
        simp [totalD, count, Finset.sum_add_distrib]
  have hfourLinear : 4 * (totalD + count) ≤ 5 * totalD := by
    omega
  have hd : 3 ≤ d := by
    have htot := hcount.trans hsum
    omega
  have hscaled :
      4 * (∑ i : I, (D i + 1) ^ 2) ≤ 5 * d * (d - 3) := by
    have hmul := Nat.mul_le_mul_left (d - 3) hfourLinear
    have hsum' : totalD ≤ d := hsum
    nlinarith
  have hpoly : 5 * d * (d - 3) ≤
      4 * (s ^ 2 + 2 * s * d + 4 * s) := by
    let t := d - 3
    have hdt : d = t + 3 := by simp [t]; omega
    have ht : t ≤ 2 * s := by omega
    have hsq : 5 * t * t ≤ 10 * s * t := by
      have h := Nat.mul_le_mul_left (5 * t) ht
      nlinarith
    have hlin : 15 * t ≤ 30 * s := by nlinarith
    rw [hdt]
    have hsub : t + 3 - 3 = t := by omega
    rw [hsub]
    nlinarith
  have hp := partnerDistance_pos d
  have hbase : s ^ 2 + 2 * s * d + 4 * s ≤ rlBudget s d := by
    unfold rlBudget
    nlinarith
  have hbudget : 4 * (s ^ 2 + 2 * s * d + 4 * s) ≤
      4 * rlBudget s d := Nat.mul_le_mul_left 4 hbase
  have := hscaled.trans (hpoly.trans hbudget)
  omega

/-- A second useful landing: a total-distance bound `sum D_i <= 2s` already
closes RL in the whole range `3s <= 2d`.  This is the uniform target for a
near-boundary cut family with at most `2s` residual coordinates. -/
theorem totalCost_le_rlBudget_of_sumDistances_le_twiceSlack
    {I : Type*} [Fintype I] (D : I → ℕ) (s d : ℕ)
    (hcard : 2 ≤ Fintype.card I)
    (hlegal : ∀ i, 4 ≤ D i)
    (hsum : (∑ i : I, D i) ≤ 2 * s)
    (hs : 3 ≤ s) (hratio : 3 * s ≤ 2 * d) :
    (∑ i : I, (D i + 1) ^ 2) ≤ rlBudget s d := by
  have hconvex :=
    sum_add_one_sq_le_total_sub_three_sq_add_twentyFive D hcard hlegal
  have htotal : 3 ≤ ∑ i : I, D i := by
    have hcount : 4 * Fintype.card I ≤ ∑ i : I, D i := by
      have h := Finset.sum_le_sum
        (s := (Finset.univ : Finset I))
        (f := fun _ : I => 4) (g := D) (fun i _ => hlegal i)
      simpa [Nat.mul_comm] using h
    omega
  have hsub : (∑ i : I, D i) - 3 ≤ 2 * s - 3 := by omega
  have hsquare := Nat.pow_le_pow_left hsub 2
  have hp := partnerDistance_pos d
  have hbudget : (2 * s - 3) ^ 2 + 25 ≤ rlBudget s d := by
    have htwo : 2 * s - 3 + 3 = 2 * s := by omega
    unfold rlBudget
    nlinarith
  exact hconvex.trans (Nat.add_le_add_right hsquare 25 |>.trans hbudget)

/-- RFC landing for a distance-dominating family of size-two cuts.  The cut family
is deliberately literal: its cardinality is `d`, each cut separates the
root from the stub and has supply size at most two, and the number of cuts
separating a demand is at least its graph distance.  Cuts may repeat. -/
theorem totalCost_le_rlBudget_of_dominatingTwoCutBasis
    {V I K : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [Fintype K]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (m₁ m₂ : I → V) (w x₀ : V) (cuts : K → Finset V)
    (s d : ℕ)
    (hcardCuts : Fintype.card K = d)
    (hcardDemands : 2 ≤ Fintype.card I)
    (hRFC : ∀ T : Finset V, w ∉ T →
      (∑ i : I, separationDemand T (m₁ i) (m₂ i)) +
        (if x₀ ∈ T then 1 else 0) ≤ cutSize G T)
    (hterminal : ∀ k, separationDemand (cuts k) w x₀ = 1)
    (hcutSize : ∀ k, cutSize G (cuts k) ≤ 2)
    (hdominates : ∀ i,
      G.dist (m₁ i) (m₂ i) ≤
        ∑ k : K, separationDemand (cuts k) (m₁ i) (m₂ i))
    (hlegal : ∀ i, 4 ≤ G.dist (m₁ i) (m₂ i))
    (hds : d ≤ 2 * s) :
    (∑ i : I, (G.dist (m₁ i) (m₂ i) + 1) ^ 2) ≤
      rlBudget s d := by
  classical
  have hsym := symmetricRootedCutCondition_of_rootForm
    G m₁ m₂ w x₀ hRFC
  have hcolumn : ∀ k,
      (∑ i : I, separationDemand (cuts k) (m₁ i) (m₂ i)) ≤ 1 := by
    intro k
    have h := hsym (cuts k)
    rw [hterminal k] at h
    have hc := hcutSize k
    exact (by omega :
      (∑ i : I, separationDemand (cuts k) (m₁ i) (m₂ i)) ≤ 1)
  have hsum : (∑ i : I, G.dist (m₁ i) (m₂ i)) ≤ d := by
    calc
      (∑ i : I, G.dist (m₁ i) (m₂ i)) ≤
          ∑ i : I, ∑ k : K,
            separationDemand (cuts k) (m₁ i) (m₂ i) :=
        Finset.sum_le_sum fun i _ => hdominates i
      _ =
          ∑ k : K, ∑ i : I,
            separationDemand (cuts k) (m₁ i) (m₂ i) := by
        rw [Finset.sum_comm]
      _ ≤ ∑ _k : K, 1 := Finset.sum_le_sum fun k _ => hcolumn k
      _ = d := by simp [hcardCuts]
  exact totalCost_le_rlBudget_of_sumDistances_le_length
    (fun i => G.dist (m₁ i) (m₂ i)) s d
    hcardDemands hlegal hsum hds

/-- Near-boundary RFC landing for a distance-dominating family of repeated
size-two cuts with at most `2s` coordinates.  Unlike the length-`d` version,
this permits the two extra coordinates naturally exposed by the
`d = 2s - 2` defect ledger.  Structural existence of the cut family remains
an explicit premise. -/
theorem totalCost_le_rlBudget_of_dominatingTwoCutFamily_twiceSlack
    {V I K : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [Fintype K]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (m₁ m₂ : I → V) (w x₀ : V) (cuts : K → Finset V)
    (s d : ℕ)
    (hcardCuts : Fintype.card K ≤ 2 * s)
    (hcardDemands : 2 ≤ Fintype.card I)
    (hRFC : ∀ T : Finset V, w ∉ T →
      (∑ i : I, separationDemand T (m₁ i) (m₂ i)) +
        (if x₀ ∈ T then 1 else 0) ≤ cutSize G T)
    (hterminal : ∀ k, separationDemand (cuts k) w x₀ = 1)
    (hcutSize : ∀ k, cutSize G (cuts k) ≤ 2)
    (hdominates : ∀ i,
      G.dist (m₁ i) (m₂ i) ≤
        ∑ k : K, separationDemand (cuts k) (m₁ i) (m₂ i))
    (hlegal : ∀ i, 4 ≤ G.dist (m₁ i) (m₂ i))
    (hs : 3 ≤ s) (hratio : 3 * s ≤ 2 * d) :
    (∑ i : I, (G.dist (m₁ i) (m₂ i) + 1) ^ 2) ≤
      rlBudget s d := by
  classical
  have hsym := symmetricRootedCutCondition_of_rootForm
    G m₁ m₂ w x₀ hRFC
  have hcolumn : ∀ k,
      (∑ i : I, separationDemand (cuts k) (m₁ i) (m₂ i)) ≤ 1 := by
    intro k
    have h := hsym (cuts k)
    rw [hterminal k] at h
    have hc := hcutSize k
    exact (by omega :
      (∑ i : I, separationDemand (cuts k) (m₁ i) (m₂ i)) ≤ 1)
  have hsumCard : (∑ i : I, G.dist (m₁ i) (m₂ i)) ≤
      Fintype.card K := by
    calc
      (∑ i : I, G.dist (m₁ i) (m₂ i)) ≤
          ∑ i : I, ∑ k : K,
            separationDemand (cuts k) (m₁ i) (m₂ i) :=
        Finset.sum_le_sum fun i _ => hdominates i
      _ = ∑ k : K, ∑ i : I,
            separationDemand (cuts k) (m₁ i) (m₂ i) := by
        rw [Finset.sum_comm]
      _ ≤ ∑ _k : K, 1 := Finset.sum_le_sum fun k _ => hcolumn k
      _ = Fintype.card K := by simp
  have hsum : (∑ i : I, G.dist (m₁ i) (m₂ i)) ≤ 2 * s :=
    hsumCard.trans hcardCuts
  exact totalCost_le_rlBudget_of_sumDistances_le_twiceSlack
    (fun i => G.dist (m₁ i) (m₂ i)) s d
    hcardDemands hlegal hsum hs hratio

/-- Equality of distance with the cut count is the special isometric case
of the dominating cut-basis theorem. -/
theorem totalCost_le_rlBudget_of_isometricTwoCutBasis
    {V I K : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [Fintype K]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (m₁ m₂ : I → V) (w x₀ : V) (cuts : K → Finset V)
    (s d : ℕ)
    (hcardCuts : Fintype.card K = d)
    (hcardDemands : 2 ≤ Fintype.card I)
    (hRFC : ∀ T : Finset V, w ∉ T →
      (∑ i : I, separationDemand T (m₁ i) (m₂ i)) +
        (if x₀ ∈ T then 1 else 0) ≤ cutSize G T)
    (hterminal : ∀ k, separationDemand (cuts k) w x₀ = 1)
    (hcutSize : ∀ k, cutSize G (cuts k) ≤ 2)
    (hisometric : ∀ i,
      G.dist (m₁ i) (m₂ i) =
        ∑ k : K, separationDemand (cuts k) (m₁ i) (m₂ i))
    (hlegal : ∀ i, 4 ≤ G.dist (m₁ i) (m₂ i))
    (hds : d ≤ 2 * s) :
    (∑ i : I, (G.dist (m₁ i) (m₂ i) + 1) ^ 2) ≤
      rlBudget s d := by
  exact totalCost_le_rlBudget_of_dominatingTwoCutBasis
    m₁ m₂ w x₀ cuts s d hcardCuts hcardDemands hRFC
    hterminal hcutSize (fun i => (hisometric i).le) hlegal hds

#print axioms totalCost_le_rlBudget_of_sumDistances_le_length
#print axioms sum_add_one_sq_le_total_sub_three_sq_add_twentyFive
#print axioms totalCost_le_rlBudget_of_sumDistances_le_twiceSlack
#print axioms totalCost_le_rlBudget_of_dominatingTwoCutBasis
#print axioms totalCost_le_rlBudget_of_dominatingTwoCutFamily_twiceSlack
#print axioms totalCost_le_rlBudget_of_isometricTwoCutBasis

end Erdos23GapGBIsometricCuts
