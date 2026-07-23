/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair, OpenAI Codex
-/
import ErdosProblems.Erdos23GapGAClosed
import ErdosProblems.Erdos23GapGBEqualityBoundary
import ErdosProblems.Erdos23GapGBAggregationArithmetic

/-!
# Erdős 23 G-B: two-demand consequences of RFC

This module composes three already-audited ingredients:

* rooted RFC implies the symmetric two-demand cut condition for each
  individual internal demand;
* G-A gives the sharp single-demand inequality `2D <= 2s+d`;
* the integer arithmetic in `Erdos23GapGBAggregationArithmetic` pays both
  quadratic costs when one of two legal even distances is four.

The result closes that literal graph-level slice of the strict BF-RL
residual.  It does not assert the missing joint estimate for two distances
strictly larger than four.
-/

namespace Erdos23GapGBTwoDemand

open scoped BigOperators
open SimpleGraph
open Erdos23GapGA
open Erdos23GapGBSeries
open Erdos23GapGBEqualityBoundary
open Erdos23GapGBAggregationArithmetic

/-- A rooted cut condition for a family contains the symmetric two-demand
cut condition formed by the root--stub pair and any one internal demand. -/
theorem twoDemandCutCondition_of_rootedCutCondition
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m₁ m₂ : I → V) (w x₀ : V)
    (hRFC : ∀ T : Finset V, w ∉ T →
      (∑ i : I, separationDemand T (m₁ i) (m₂ i)) +
        (if x₀ ∈ T then 1 else 0) ≤ cutSize G T)
    (i : I) :
    TwoDemandCutCondition G w x₀ (m₁ i) (m₂ i) := by
  classical
  have hsym := symmetricRootedCutCondition_of_rootForm
    G m₁ m₂ w x₀ hRFC
  intro T
  have hterm : separationDemand T (m₁ i) (m₂ i) ≤
      ∑ j : I, separationDemand T (m₁ j) (m₂ j) := by
    exact Finset.single_le_sum
      (fun j _ => Nat.zero_le (separationDemand T (m₁ j) (m₂ j)))
      (Finset.mem_univ i)
  have h := hsym T
  omega

/-- G-A's `SE2` bound for any individual demand, directly from rooted RFC. -/
theorem two_mul_dist_le_twice_slack_add_length_of_rootedCutCondition
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀} (m₁ m₂ : I → V)
    (hconn : G.Connected) (hP : IsGeodesic P)
    (hRFC : ∀ T : Finset V, w ∉ T →
      (∑ i : I, separationDemand T (m₁ i) (m₂ i)) +
        (if x₀ ∈ T then 1 else 0) ≤ cutSize G T)
    (i : I) :
    2 * G.dist (m₁ i) (m₂ i) ≤ 2 * slack P + P.length := by
  obtain ⟨Q, hQ⟩ := hconn.exists_walk_length_eq_dist (m₁ i) (m₂ i)
  have hQgeo : IsGeodesic Q := hQ
  have hbounds := gapGA_symmetric_bounds P Q hP hQgeo
    (twoDemandCutCondition_of_rootedCutCondition G m₁ m₂ w x₀ hRFC i)
  rw [hQ] at hbounds
  exact hbounds.2

/-- Complete graph-level closure of the two-internal-demand slice when one
distance is four.  The other distance is forced even by the proper Boolean
coloring, receives `SE2` from RFC, and the exact integer convex calculation
pays both squares in the strict BF-RL budget. -/
theorem totalCost_le_rlBudget_of_twoDemands_oneDistanceFour
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    (m₁ m₂ : Fin 2 → V) (color : G.Coloring Bool)
    (hconn : G.Connected) (hP : IsGeodesic P)
    (hRFC : ∀ T : Finset V, w ∉ T →
      (∑ i : Fin 2, separationDemand T (m₁ i) (m₂ i)) +
        (if x₀ ∈ T then 1 else 0) ≤ cutSize G T)
    (hlegal : ∀ i, 4 ≤ G.dist (m₁ i) (m₂ i))
    (hsame : ∀ i, color (m₁ i) = color (m₂ i))
    (hfour : G.dist (m₁ 0) (m₂ 0) = 4)
    (hs : 5 ≤ slack P) (hn : 13 ≤ slack P + P.length)
    (hd : 3 ≤ P.length) (hds : P.length < 2 * slack P)
    (hresidual :
      2 * slack P * partnerDistance P.length < (P.length + 1) ^ 2) :
    (∑ i : Fin 2, (G.dist (m₁ i) (m₂ i) + 1) ^ 2) ≤
      rlBudget (slack P) P.length := by
  have heven : Even (G.dist (m₁ 1) (m₂ 1)) :=
    Coloring.even_dist_of_eq hconn color (hsame 1)
  obtain ⟨B, hB⟩ := heven
  have hBpos : 2 ≤ B := by
    have := hlegal 1
    omega
  have hSE2raw :=
    two_mul_dist_le_twice_slack_add_length_of_rootedCutCondition
      m₁ m₂ hconn hP hRFC (1 : Fin 2)
  have hSE2 : 4 * B ≤ 2 * slack P + P.length := by
    rw [hB] at hSE2raw
    omega
  have harith := twoCosts_le_rlBudget_of_oneDistanceFour
    hBpos hSE2 hs hn hd hds hresidual
  have hBtwo : G.dist (m₁ 1) (m₂ 1) = 2 * B := by omega
  have hsum :
      (∑ i : Fin 2, (G.dist (m₁ i) (m₂ i) + 1) ^ 2) =
        25 + (2 * B + 1) ^ 2 := by
    rw [Fin.sum_univ_two]
    rw [hfour, hBtwo]
    norm_num
  rw [hsum]
  exact harith

/-- Index-free form: either of the two internal demands may be the
distance-four demand. -/
theorem totalCost_le_rlBudget_of_twoDemands_existsDistanceFour
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    (m₁ m₂ : Fin 2 → V) (color : G.Coloring Bool)
    (hconn : G.Connected) (hP : IsGeodesic P)
    (hRFC : ∀ T : Finset V, w ∉ T →
      (∑ i : Fin 2, separationDemand T (m₁ i) (m₂ i)) +
        (if x₀ ∈ T then 1 else 0) ≤ cutSize G T)
    (hlegal : ∀ i, 4 ≤ G.dist (m₁ i) (m₂ i))
    (hsame : ∀ i, color (m₁ i) = color (m₂ i))
    (hfour : ∃ i, G.dist (m₁ i) (m₂ i) = 4)
    (hs : 5 ≤ slack P) (hn : 13 ≤ slack P + P.length)
    (hd : 3 ≤ P.length) (hds : P.length < 2 * slack P)
    (hresidual :
      2 * slack P * partnerDistance P.length < (P.length + 1) ^ 2) :
    (∑ i : Fin 2, (G.dist (m₁ i) (m₂ i) + 1) ^ 2) ≤
      rlBudget (slack P) P.length := by
  obtain ⟨i, hi⟩ := hfour
  fin_cases i
  · exact totalCost_le_rlBudget_of_twoDemands_oneDistanceFour
      m₁ m₂ color hconn hP hRFC hlegal hsame hi
      hs hn hd hds hresidual
  · let m₁' : Fin 2 → V := fun j ↦ m₁ j.rev
    let m₂' : Fin 2 → V := fun j ↦ m₂ j.rev
    have hRFC' : ∀ T : Finset V, w ∉ T →
        (∑ j : Fin 2, separationDemand T (m₁' j) (m₂' j)) +
          (if x₀ ∈ T then 1 else 0) ≤ cutSize G T := by
      intro T hw
      simpa [m₁', m₂', Fin.sum_univ_two, add_comm] using hRFC T hw
    have hlegal' : ∀ j, 4 ≤ G.dist (m₁' j) (m₂' j) := by
      intro j
      exact hlegal j.rev
    have hsame' : ∀ j, color (m₁' j) = color (m₂' j) := by
      intro j
      exact hsame j.rev
    have hfour' : G.dist (m₁' 0) (m₂' 0) = 4 := by
      simpa [m₁', m₂'] using hi
    have h := totalCost_le_rlBudget_of_twoDemands_oneDistanceFour
      m₁' m₂' color hconn hP hRFC' hlegal' hsame' hfour'
      hs hn hd hds hresidual
    simpa [m₁', m₂', Fin.sum_univ_two, add_comm] using h

#print axioms twoDemandCutCondition_of_rootedCutCondition
#print axioms two_mul_dist_le_twice_slack_add_length_of_rootedCutCondition
#print axioms totalCost_le_rlBudget_of_twoDemands_oneDistanceFour
#print axioms totalCost_le_rlBudget_of_twoDemands_existsDistanceFour

end Erdos23GapGBTwoDemand
