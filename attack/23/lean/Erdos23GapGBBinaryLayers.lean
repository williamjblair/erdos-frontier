/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair, OpenAI Codex
-/
import ErdosProblems.Erdos23GapGBJoint

/-!
# Erdős 23 G-B: binary BFS layers with level-aligned demands

This module closes a proper multi-demand subregime of the bridge-free RL
frontier.  The graph-facing datum is the threshold-cut incidence matrix:
rows are internal demands and columns are the `d` BFS level cuts.  A demand
is *level aligned* exactly when the number of level cuts it crosses equals
its graph distance.  Binary BFS layers give each column one of the exact
residual capacities `0`, `1`, or `3`; these are encoded as
`active + 2 * high`, where `active, high` are zero-one profiles and
`high <= active`.

The theorem does not assert that arbitrary demands are level aligned.  That
hypothesis is essential and is falsified by an exact residual fixture in
`compute23/gate3/agent_weighted_dual/audit_unaligned_fixture.py`.
-/

namespace Erdos23GapGBBinaryLayers

open scoped BigOperators
open SimpleGraph
open Erdos23GapGA
open Erdos23GapGBJoint
open Erdos23GapGBSeries

/-- Elementary pointwise form of the binary-column pair bound.  If a column
has residual capacity `active + 2*high`, two columns jointly carry at most
`active₁*active₂ + 2*high₁*high₂` rows. -/
theorem pairLoad_le_binaryPairCapacity
    {pairLoad active₁ active₂ high₁ high₂ : ℕ}
    (ha₁ : active₁ ≤ 1) (ha₂ : active₂ ≤ 1)
    (hh₁ : high₁ ≤ active₁) (hh₂ : high₂ ≤ active₂)
    (hleft : pairLoad ≤ active₁ + 2 * high₁)
    (hright : pairLoad ≤ active₂ + 2 * high₂) :
    pairLoad ≤ active₁ * active₂ + 2 * high₁ * high₂ := by
  by_cases hactive₁ : active₁ = 0
  · subst active₁
    have : high₁ = 0 := by omega
    subst high₁
    simp_all
  by_cases hactive₂ : active₂ = 0
  · subst active₂
    have : high₂ = 0 := by omega
    subst high₂
    simp_all
  have hactive₁' : active₁ = 1 := by omega
  have hactive₂' : active₂ = 1 := by omega
  subst active₁
  subst active₂
  by_cases hhigh₁ : high₁ = 0
  · subst high₁
    simp_all
  by_cases hhigh₂ : high₂ = 0
  · subst high₂
    simp_all
  have hhigh₁' : high₁ = 1 := by omega
  have hhigh₂' : high₂ = 1 := by omega
  subst high₁
  subst high₂
  omega

/-- Exact denominator-cleared arithmetic envelope for a binary BFS layer
profile.  `L` is the number of active gaps and `H` the number whose two
endpoint levels are both doubled. -/
theorem binaryLayer_intervalEnvelope
    {s d L H : ℕ}
    (hL : L ≤ d) (hHL : H ≤ L) (hLH : L + H ≤ 2 * s)
    (hHs : H + 1 ≤ s) :
    4 * L ^ 2 + 8 * H ^ 2 + 9 * L + 18 * H ≤
      4 * s ^ 2 + 8 * s * d + 16 * s := by
  by_cases hdlo : d ≤ s - 1
  · have hLd : L ≤ s - 1 := hL.trans hdlo
    have hHd : H ≤ s - 1 := hHL.trans hLd
    nlinarith [sq_nonneg (s - 1 - L), sq_nonneg (L - H),
      sq_nonneg (s - 1 - H)]
  · have hsd : s ≤ d + 1 := by omega
    by_cases hdhi : s + 1 ≤ d
    · by_cases hHd : H ≤ 2 * s - d
      · nlinarith [sq_nonneg (d - L), sq_nonneg (2 * s - d - H),
          sq_nonneg H]
      · have hHlarge : 2 * s - d ≤ H := by omega
        have hLsum : L ≤ 2 * s - H := by omega
        nlinarith [sq_nonneg (2 * s - H - L),
          sq_nonneg (H - (2 * s - d)), sq_nonneg (s - 1 - H)]
    · have hdmid : d ≤ s := by omega
      have hLs : L ≤ s := hL.trans hdmid
      have hHsm : H ≤ s - 1 := by omega
      nlinarith [sq_nonneg (s - L), sq_nonneg (s - 1 - H),
        sq_nonneg (L - H)]

/-- The RL budget contains the parity-independent binary-layer envelope,
because the partner distance is always positive. -/
theorem parityIndependentBudget_le_rlBudget (s d : ℕ) :
    s ^ 2 + 2 * s * d + 4 * s ≤ rlBudget s d := by
  have hp := partnerDistance_pos d
  unfold rlBudget
  nlinarith

/-- Matrix form of the complete binary-layer argument.

`cross i r` is the `0/1` indicator that demand `i` crosses BFS level gap
`r`.  Level alignment is the exact identity
`D i = sum_r cross i r`.  RFC together with simplicity of the supply graph
gives the column-capacity hypothesis.  The remaining four inequalities are
the exact finite counts supplied by a binary BFS profile with at most `s`
extra vertices among levels `0,...,d`.
-/
theorem totalCost_le_rlBudget_of_binaryLayerAlignedMatrix
    {I R : Type*} [Fintype I] [Fintype R]
    (D : I → ℕ) (cross : I → R → ℕ)
    (active high : R → ℕ) (s d : ℕ)
    (hcross : ∀ i r, cross i r ≤ 1)
    (haligned : ∀ i, D i = ∑ r : R, cross i r)
    (hcolumn : ∀ r, (∑ i : I, cross i r) ≤ active r + 2 * high r)
    (hactive : ∀ r, active r ≤ 1)
    (hhigh : ∀ r, high r ≤ active r)
    (hlegal : ∀ i, 4 ≤ D i)
    (hL : (∑ r : R, active r) ≤ d)
    (hHL : (∑ r : R, high r) ≤ ∑ r : R, active r)
    (hLH : (∑ r : R, active r) + (∑ r : R, high r) ≤ 2 * s)
    (hHs : (∑ r : R, high r) + 1 ≤ s) :
    (∑ i : I, (D i + 1) ^ 2) ≤ rlBudget s d := by
  classical
  let L := ∑ r : R, active r
  let H := ∑ r : R, high r
  let totalD := ∑ i : I, D i
  let totalDsq := ∑ i : I, (D i) ^ 2

  have hlinear : totalD ≤ L + 2 * H := by
    calc
      totalD = ∑ r : R, ∑ i : I, cross i r := by
        simp only [totalD, haligned]
        rw [Finset.sum_comm]
      _ ≤ ∑ r : R, (active r + 2 * high r) := by
        exact Finset.sum_le_sum fun r _ => hcolumn r
      _ = L + 2 * H := by
        simp [L, H, Finset.sum_add_distrib, Finset.mul_sum]

  have hpair (r q : R) :
      (∑ i : I, cross i r * cross i q) ≤
        active r * active q + 2 * high r * high q := by
    have hleft : (∑ i : I, cross i r * cross i q) ≤
        ∑ i : I, cross i r := by
      exact Finset.sum_le_sum fun i _ => by
        have := hcross i q
        nlinarith
    have hright : (∑ i : I, cross i r * cross i q) ≤
        ∑ i : I, cross i q := by
      exact Finset.sum_le_sum fun i _ => by
        have := hcross i r
        nlinarith
    exact pairLoad_le_binaryPairCapacity
      (hactive r) (hactive q) (hhigh r) (hhigh q)
      (hleft.trans (hcolumn r)) (hright.trans (hcolumn q))

  have hsquare : totalDsq ≤ L ^ 2 + 2 * H ^ 2 := by
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
      _ ≤ ∑ r : R, ∑ q : R,
          (active r * active q + 2 * high r * high q) := by
        exact Finset.sum_le_sum fun r _ =>
          Finset.sum_le_sum fun q _ => hpair r q
      _ = L ^ 2 + 2 * H ^ 2 := by
        simp [L, H, pow_two, Finset.sum_add_distrib,
          Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

  have hcard : 4 * Fintype.card I ≤ totalD := by
    have hsum := Finset.sum_le_sum
      (s := (Finset.univ : Finset I)) (f := fun _ : I => 4) (g := D)
      (fun i _ => hlegal i)
    simpa [totalD, Nat.mul_comm] using hsum

  have hscaled : 4 * (∑ i : I, (D i + 1) ^ 2) ≤
      4 * L ^ 2 + 8 * H ^ 2 + 9 * L + 18 * H := by
    have hcost :
        4 * (∑ i : I, (D i + 1) ^ 2) =
          4 * totalDsq + 8 * totalD + 4 * Fintype.card I := by
      calc
        4 * (∑ i : I, (D i + 1) ^ 2) =
            ∑ i : I, 4 * (D i + 1) ^ 2 := by
              rw [Finset.mul_sum]
        _ = ∑ i : I, (4 * (D i) ^ 2 + 8 * D i + 4) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
        _ = 4 * totalDsq + 8 * totalD + 4 * Fintype.card I := by
              simp [totalDsq, totalD, Finset.sum_add_distrib,
                Finset.mul_sum, Nat.mul_comm]
    rw [hcost]
    nlinarith

  have henvelope :
      4 * L ^ 2 + 8 * H ^ 2 + 9 * L + 18 * H ≤
        4 * s ^ 2 + 8 * s * d + 16 * s := by
    exact binaryLayer_intervalEnvelope hL hHL hLH hHs
  have hbase := parityIndependentBudget_le_rlBudget s d
  have hfourBase :
      4 * s ^ 2 + 8 * s * d + 16 * s ≤ 4 * rlBudget s d := by
    nlinarith
  have hfour := hscaled.trans (henvelope.trans hfourBase)
  omega

/-- The upper BFS-level cut at threshold `k`: vertices whose level is
strictly greater than `k`.  Gap `k` lies between levels `k` and `k+1`. -/
def levelUpperCut {V : Type*} [Fintype V] [DecidableEq V]
    (level : V → ℕ) (k : ℕ) : Finset V :=
  Finset.univ.filter fun v => k < level v

@[simp]
theorem mem_levelUpperCut {V : Type*} [Fintype V] [DecidableEq V]
    (level : V → ℕ) (k : ℕ) (v : V) :
    v ∈ levelUpperCut level k ↔ k < level v := by
  simp [levelUpperCut]

/-- The vertices on one exact BFS level. -/
def levelLayer {V : Type*} [Fintype V] [DecidableEq V]
    (level : V → ℕ) (k : ℕ) : Finset V :=
  Finset.univ.filter fun v => level v = k

@[simp]
theorem mem_levelLayer {V : Type*} [Fintype V] [DecidableEq V]
    (level : V → ℕ) (k : ℕ) (v : V) :
    v ∈ levelLayer level k ↔ level v = k := by
  simp [levelLayer]

/-- Simplicity is used exactly here.  If every supply edge joins consecutive
levels, the number of supply edges crossing the upper cut at gap `r` is at
most the product of the two adjacent layer cardinalities. -/
theorem cutSize_levelUpperCut_le_layerProduct
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (level : V → ℕ)
    (hstep : ∀ {u v : V}, G.Adj u v → Nat.dist (level u) (level v) = 1)
    (r : ℕ) :
    cutSize G (levelUpperCut level r) ≤
      (levelLayer level r).card * (levelLayer level (r + 1)).card := by
  classical
  let T := levelUpperCut level r
  let A := levelLayer level r
  let C := levelLayer level (r + 1)
  have hvertex (v : V) (hv : v ∈ T) :
      (G.neighborFinset v \ T).card ≤
        if level v = r + 1 then A.card else 0 := by
    by_cases hvr : level v = r + 1
    · rw [if_pos hvr]
      apply Finset.card_le_card
      intro u hu
      have huv : G.Adj v u := by
        exact (SimpleGraph.mem_neighborFinset (G := G) (v := v) u).mp
          (Finset.mem_sdiff.mp hu).1
      have huT : u ∉ T := (Finset.mem_sdiff.mp hu).2
      have hvT : r < level v := by simpa [T] using hv
      have hulow : level u ≤ r := by simpa [T] using huT
      have hdist := hstep huv.symm
      have hur : level u = r := by
        rw [hvr] at hdist
        rw [Nat.dist_eq_sub_of_le (by omega : level u ≤ r + 1)] at hdist
        omega
      simpa [A] using hur
    · rw [if_neg hvr]
      have hempty : G.neighborFinset v \ T = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro u hu
        have huv : G.Adj v u := by
          exact (SimpleGraph.mem_neighborFinset (G := G) (v := v) u).mp
            (Finset.mem_sdiff.mp hu).1
        have huT : u ∉ T := (Finset.mem_sdiff.mp hu).2
        have hvhigh : r < level v := by simpa [T] using hv
        have hulow : level u ≤ r := by simpa [T] using huT
        have hdist := hstep huv.symm
        rw [Nat.dist_eq_sub_of_le (by omega : level u ≤ level v)] at hdist
        have : level v = r + 1 := by omega
        exact hvr this
      simp [hempty]
  unfold cutSize
  calc
    (∑ v ∈ T, (G.neighborFinset v \ T).card) ≤
        ∑ v ∈ T, if level v = r + 1 then A.card else 0 := by
          exact Finset.sum_le_sum fun v hv => hvertex v hv
    _ = ∑ v ∈ T.filter (fun v => level v = r + 1), A.card := by
          rw [Finset.sum_filter]
    _ = ∑ v ∈ C, A.card := by
          apply Finset.sum_congr
          · ext v
            simp [T, C]
            omega
          · simp
    _ = A.card * C.card := by
          simp [Nat.mul_comm]
    _ = (levelLayer level r).card *
        (levelLayer level (r + 1)).card := by rfl

/-- Graph-facing binary-layer theorem.

The explicitly quantified cut-profile hypothesis is the exact place where
simple binary BFS layers enter: the level-`r`/level-`r+1` pair has at most
`1`, `2`, or `4` simple supply edges, and the rooted terminal consumes one,
leaving `active r + 2*high r` units.  Thus no multicommodity-routing or
vertex-load assertion is hidden in this surface.

`haligned` is literal equality between graph distance and BFS-level span.
Vertices not incident with a demand may lie beyond level `d`; only the two
endpoints of every internal demand are required to lie in levels `0,...,d`.
-/
theorem totalCost_le_rlBudget_of_binaryBfsCutProfile_levelAligned
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (w x₀ : V) (m₁ m₂ : I → V) (level : V → ℕ)
    (s d : ℕ) (active high : Fin d → ℕ)
    (hroot : level w = 0) (hstub : level x₀ = d)
    (hendpoint₁ : ∀ i, level (m₁ i) ≤ d)
    (hendpoint₂ : ∀ i, level (m₂ i) ≤ d)
    (haligned : ∀ i,
      G.dist (m₁ i) (m₂ i) = Nat.dist (level (m₁ i)) (level (m₂ i)))
    (hRFC : ∀ T : Finset V, w ∉ T →
      (∑ i : I, separationDemand T (m₁ i) (m₂ i)) +
        (if x₀ ∈ T then 1 else 0) ≤ cutSize G T)
    (hcutProfile : ∀ r : Fin d,
      cutSize G (levelUpperCut level r.1) ≤
        active r + 2 * high r + 1)
    (hactive : ∀ r, active r ≤ 1)
    (hhigh : ∀ r, high r ≤ active r)
    (hlegal : ∀ i, 4 ≤ G.dist (m₁ i) (m₂ i))
    (hHL : (∑ r : Fin d, high r) ≤ ∑ r : Fin d, active r)
    (hLH : (∑ r : Fin d, active r) + (∑ r : Fin d, high r) ≤ 2 * s)
    (hHs : (∑ r : Fin d, high r) + 1 ≤ s) :
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
      (∑ i : I, cross i r) ≤ active r + 2 * high r := by
    intro r
    have hw : w ∉ levelUpperCut level r.1 := by
      simp [hroot]
    have hx : x₀ ∈ levelUpperCut level r.1 := by
      simp [hstub, r.2]
    have hcut := hRFC (levelUpperCut level r.1) hw
    simp only [hx, if_true] at hcut
    exact Nat.le_of_add_le_add_right
      (hcut.trans (hcutProfile r))

  have hLprofile : (∑ r : Fin d, active r) ≤ d := by
    calc
      (∑ r : Fin d, active r) ≤ ∑ _r : Fin d, 1 := by
        exact Finset.sum_le_sum fun r _ => hactive r
      _ = d := by simp

  apply totalCost_le_rlBudget_of_binaryLayerAlignedMatrix
    (fun i => G.dist (m₁ i) (m₂ i)) cross active high s d
    hcross hmatrixAligned hcolumn hactive hhigh hlegal
  · exact hLprofile
  · exact hHL
  · exact hLH
  · exact hHs

/-- Raw simple-graph wrapper for the preceding theorem.  The hypothesis
`hpairProfile` identifies the adjacent BFS-layer product with its exact
binary value `1`, `2`, or `4`; `cutSize_levelUpperCut_le_layerProduct`
derives the required cut profile, so simplicity is no longer hidden in a
numeric cut-capacity premise. -/
theorem totalCost_le_rlBudget_of_binaryBfsLayers_levelAligned
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (w x₀ : V) (m₁ m₂ : I → V) (level : V → ℕ)
    (s d : ℕ) (active high : Fin d → ℕ)
    (hstep : ∀ {u v : V}, G.Adj u v →
      Nat.dist (level u) (level v) = 1)
    (hpairProfile : ∀ r : Fin d,
      (levelLayer level r.1).card *
          (levelLayer level (r.1 + 1)).card =
        active r + 2 * high r + 1)
    (hroot : level w = 0) (hstub : level x₀ = d)
    (hendpoint₁ : ∀ i, level (m₁ i) ≤ d)
    (hendpoint₂ : ∀ i, level (m₂ i) ≤ d)
    (haligned : ∀ i,
      G.dist (m₁ i) (m₂ i) = Nat.dist (level (m₁ i)) (level (m₂ i)))
    (hRFC : ∀ T : Finset V, w ∉ T →
      (∑ i : I, separationDemand T (m₁ i) (m₂ i)) +
        (if x₀ ∈ T then 1 else 0) ≤ cutSize G T)
    (hactive : ∀ r, active r ≤ 1)
    (hhigh : ∀ r, high r ≤ active r)
    (hlegal : ∀ i, 4 ≤ G.dist (m₁ i) (m₂ i))
    (hHL : (∑ r : Fin d, high r) ≤ ∑ r : Fin d, active r)
    (hLH : (∑ r : Fin d, active r) + (∑ r : Fin d, high r) ≤ 2 * s)
    (hHs : (∑ r : Fin d, high r) + 1 ≤ s) :
    (∑ i : I, (G.dist (m₁ i) (m₂ i) + 1) ^ 2) ≤ rlBudget s d := by
  apply totalCost_le_rlBudget_of_binaryBfsCutProfile_levelAligned
    w x₀ m₁ m₂ level s d active high hroot hstub
    hendpoint₁ hendpoint₂ haligned hRFC
  · intro r
    exact (cutSize_levelUpperCut_le_layerProduct level hstep r.1).trans_eq
      (hpairProfile r)
  · exact hactive
  · exact hhigh
  · exact hlegal
  · exact hHL
  · exact hLH
  · exact hHs

#print axioms pairLoad_le_binaryPairCapacity
#print axioms binaryLayer_intervalEnvelope
#print axioms parityIndependentBudget_le_rlBudget
#print axioms totalCost_le_rlBudget_of_binaryLayerAlignedMatrix
#print axioms totalCost_le_rlBudget_of_binaryBfsCutProfile_levelAligned
#print axioms cutSize_levelUpperCut_le_layerProduct
#print axioms totalCost_le_rlBudget_of_binaryBfsLayers_levelAligned

end Erdos23GapGBBinaryLayers
