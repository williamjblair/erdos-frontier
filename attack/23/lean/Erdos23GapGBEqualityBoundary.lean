/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair, OpenAI Codex
-/
import ErdosProblems.Erdos23GapGBJoint
import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings

/-!
# Erdős 23 G-B: the `d = 2s` equality boundary

This module closes the full bridge-free equality-boundary route in the exact
canonical objects used by the corridor reduction.  It proves RL when
`d = 2s`; no unrestricted RL statement is introduced.
-/

namespace Erdos23GapGBEqualityBoundary

open scoped BigOperators
open SimpleGraph
open Erdos23GapGA
open Erdos23GapGBSeries
open Erdos23GapGBJoint

/-- If neither endpoint is the terminal articulation, the internal boundary
cuts record the block-coordinate distance exactly. -/
theorem blockCoordinate_boundarySeparation_eq_dist_of_lt
    {s a b : ℕ} (ha : a < s) (hb : b < s) :
    (∑ k : Fin (s - 1),
      separation (decide (a < k.1 + 1)) (decide (b < k.1 + 1))) =
      Nat.dist a b := by
  classical
  rw [show (∑ k : Fin (s - 1),
      separation (decide (a < k.1 + 1)) (decide (b < k.1 + 1))) =
      ∑ k ∈ Finset.range (s - 1),
        separation (decide (a < k + 1)) (decide (b < k + 1)) by
    simpa using Fin.sum_univ_eq_sum_range
      (fun k => separation (decide (a < k + 1)) (decide (b < k + 1)))
      (s - 1)]
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab]
    calc
      (∑ k ∈ Finset.range (s - 1),
          separation (decide (a < k + 1)) (decide (b < k + 1))) =
          ∑ k ∈ Finset.range (s - 1),
            if a ≤ k ∧ k < b then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro k hk
              by_cases hak : a ≤ k <;> by_cases hkb : k < b <;>
                simp [separation, hak, hkb] <;> omega
      _ = (Finset.Ico a b).card := by
        rw [Finset.sum_boole]
        apply congrArg Finset.card
        ext k
        simp
        omega
      _ = b - a := by simp
  · rw [Nat.dist_eq_sub_of_le_right hba]
    calc
      (∑ k ∈ Finset.range (s - 1),
          separation (decide (a < k + 1)) (decide (b < k + 1))) =
          ∑ k ∈ Finset.range (s - 1),
            if b ≤ k ∧ k < a then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro k hk
              by_cases hbk : b ≤ k <;> by_cases hka : k < a <;>
                simp [separation, hbk, hka] <;> omega
      _ = (Finset.Ico b a).card := by
        rw [Finset.sum_boole]
        apply congrArg Finset.card
        ext k
        simp
        omega
      _ = a - b := by simp

/-- The block-boundary cuts retain every threshold except the terminal
threshold.  Consequently their separation count loses at most one unit of
the natural distance between two block coordinates. -/
theorem blockCoordinate_dist_le_boundarySeparation_add_one
    {s a b : ℕ} (ha : a ≤ s) (hb : b ≤ s) :
    Nat.dist a b ≤
      (∑ k : Fin (s - 1),
        separation (decide (a < k.1 + 1)) (decide (b < k.1 + 1))) + 1 := by
  classical
  by_cases ha' : a < s
  · by_cases hb' : b < s
    · rw [blockCoordinate_boundarySeparation_eq_dist_of_lt ha' hb']
      omega
    · have hbs : b = s := by omega
      subst b
      rcases le_total a s with has | hsa
      · rw [Nat.dist_eq_sub_of_le has]
        rw [show (∑ k : Fin (s - 1),
            separation (decide (a < k.1 + 1)) (decide (s < k.1 + 1))) =
            s - 1 - a by
          rw [show (∑ k : Fin (s - 1),
              separation (decide (a < k.1 + 1)) (decide (s < k.1 + 1))) =
              ∑ k ∈ Finset.range (s - 1),
                separation (decide (a < k + 1)) (decide (s < k + 1)) by
            simpa using Fin.sum_univ_eq_sum_range
              (fun k => separation (decide (a < k + 1))
                (decide (s < k + 1))) (s - 1)]
          calc
            (∑ k ∈ Finset.range (s - 1),
                separation (decide (a < k + 1)) (decide (s < k + 1))) =
                ∑ k ∈ Finset.range (s - 1), if a ≤ k then 1 else 0 := by
                  apply Finset.sum_congr rfl
                  intro k hk
                  have hklt : k < s - 1 := Finset.mem_range.mp hk
                  by_cases hak : a ≤ k <;>
                    simp [separation, hak, show ¬s < k + 1 by omega]
            _ = (Finset.Ico a (s - 1)).card := by
              rw [Finset.sum_boole]
              apply congrArg Finset.card
              ext k
              simp
              omega
            _ = s - 1 - a := by simp]
        omega
      · have : s = a := by omega
        subst a
        simp [Nat.dist]
  · have has : a = s := by omega
    subst a
    by_cases hb' : b < s
    · rw [Nat.dist_eq_sub_of_le_right hb]
      rw [show (∑ k : Fin (s - 1),
          separation (decide (s < k.1 + 1)) (decide (b < k.1 + 1))) =
          s - 1 - b by
        rw [show (∑ k : Fin (s - 1),
            separation (decide (s < k.1 + 1)) (decide (b < k.1 + 1))) =
            ∑ k ∈ Finset.range (s - 1),
              separation (decide (s < k + 1)) (decide (b < k + 1)) by
          simpa using Fin.sum_univ_eq_sum_range
            (fun k => separation (decide (s < k + 1))
              (decide (b < k + 1))) (s - 1)]
        calc
          (∑ k ∈ Finset.range (s - 1),
              separation (decide (s < k + 1)) (decide (b < k + 1))) =
              ∑ k ∈ Finset.range (s - 1), if b ≤ k then 1 else 0 := by
                apply Finset.sum_congr rfl
                intro k hk
                have hklt : k < s - 1 := Finset.mem_range.mp hk
                by_cases hbk : b ≤ k <;>
                  simp [separation, hbk, show ¬s < k + 1 by omega]
          _ = (Finset.Ico b (s - 1)).card := by
            rw [Finset.sum_boole]
            apply congrArg Finset.card
            ext k
            simp
            omega
          _ = s - 1 - b := by simp]
      omega
    · have hbs : b = s := by omega
      subst b
      simp [Nat.dist]

/-- Finite-set form of the internal block-boundary cut.  The index `k`
corresponds to the articulation at corridor coordinate `2*(k+1)`. -/
noncomputable def boundaryLeftCut
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ : V} (P : G.Walk w x₀) (k : ℕ) : Finset V := by
  classical
  exact (corridorLeftRegion P (2 * k + 1)).toFinset

@[simp]
theorem mem_boundaryLeftCut
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ x : V} (P : G.Walk w x₀) (k : ℕ) :
    x ∈ boundaryLeftCut P k ↔ x ∈ corridorLeftRegion P (2 * k + 1) := by
  classical
  simp [boundaryLeftCut]

/-- Every extreme-attachment interval is contained in the corridor edge
range. -/
theorem offCorridorComponentIntervalEdges_subset_range
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ : V} (P : G.Walk w x₀)
    (C : OffCorridorComponent P) :
    offCorridorComponentIntervalEdges P C ⊆ Finset.range P.length := by
  classical
  intro j hj
  let A := offCorridorAttachmentIndices P C
  by_cases hA : A.Nonempty
  · have hjIco : j ∈ Finset.Ico (A.min' hA) (A.max' hA) := by
      simpa [offCorridorComponentIntervalEdges, A, hA] using hj
    have hmaxMem : A.max' hA ∈ offCorridorAttachmentIndices P C := by
      simpa [A] using A.max'_mem hA
    have hmaxLe := (mem_offCorridorAttachmentIndices P C (A.max' hA)).1 hmaxMem
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_Ico.mp hjIco).2 hmaxLe.1)
  · simp [offCorridorComponentIntervalEdges, A, hA] at hj

/-- A two-edge interval identity determines both extreme attachments and
bounds every other attachment between them. -/
theorem attachment_extrema_of_interval_eq_two
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ : V} (P : G.Walk w x₀)
    (C : OffCorridorComponent P) (l : ℕ)
    (hinterval : offCorridorComponentIntervalEdges P C =
      Finset.Ico l (l + 2)) :
    l ∈ offCorridorAttachmentIndices P C ∧
      l + 2 ∈ offCorridorAttachmentIndices P C ∧
      ∀ j ∈ offCorridorAttachmentIndices P C, l ≤ j ∧ j ≤ l + 2 := by
  classical
  let A := offCorridorAttachmentIndices P C
  have hnonempty : (offCorridorComponentIntervalEdges P C).Nonempty := by
    rw [hinterval]
    exact ⟨l, by simp⟩
  have hA : A.Nonempty := by
    by_contra hempty
    have : offCorridorComponentIntervalEdges P C = ∅ := by
      simp [offCorridorComponentIntervalEdges, A, hempty]
    rw [this] at hnonempty
    exact Finset.not_nonempty_empty hnonempty
  have hdef : offCorridorComponentIntervalEdges P C =
      Finset.Ico (A.min' hA) (A.max' hA) := by
    simp [offCorridorComponentIntervalEdges, A, hA]
  have hcard : (Finset.Ico (A.min' hA) (A.max' hA)).card = 2 := by
    rw [← hdef, hinterval]
    simp
  have hdiff : A.max' hA - A.min' hA = 2 := by
    simpa [Nat.card_Ico] using hcard
  have hlmem : l ∈ Finset.Ico (A.min' hA) (A.max' hA) := by
    rw [← hdef, hinterval]
    simp
  have hl1mem : l + 1 ∈ Finset.Ico (A.min' hA) (A.max' hA) := by
    rw [← hdef, hinterval]
    simp
  have hmin : A.min' hA = l := by
    have hl := Finset.mem_Ico.mp hlmem
    have hl1 := Finset.mem_Ico.mp hl1mem
    omega
  have hmax : A.max' hA = l + 2 := by omega
  constructor
  · simpa [A, hmin] using A.min'_mem hA
  constructor
  · simpa [A, hmax] using A.max'_mem hA
  · intro j hj
    have hjA : j ∈ A := by simpa [A] using hj
    have hminLe := A.min'_le j hjA
    have hleMax := A.le_max' j hjA
    omega

/-- Every canonical component in the double-slack equality case is one of
the even two-edge tiles, not merely every tile represented by some
component. -/
theorem IsGeodesic.every_offCorridorComponent_is_even_tile
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ : V} {P : G.Walk w x₀}
    (hP : IsGeodesic P) (hdouble : P.length = 2 * slack P)
    (hnonbridge : ∀ i < P.length,
      ¬G.IsBridge s(P.getVert i, P.getVert (i + 1)))
    (C : OffCorridorComponent P) :
    ∃ k < slack P, offCorridorComponentIntervalEdges P C =
      Finset.Ico (2 * k) (2 * k + 2) := by
  classical
  obtain ⟨htiles, hdisjoint, hunit⟩ :=
    Erdos23GapGBJoint.IsGeodesic.doubleSlack_allNonbridge_rigidity
      hP hdouble hnonbridge
  have hnonempty : (offCorridorComponentIntervalEdges P C).Nonempty := by
    apply Finset.card_pos.mp
    have hc := (hunit C).2
    omega
  obtain ⟨j, hj⟩ := hnonempty
  have hjlt : j < P.length := Finset.mem_range.mp
    (offCorridorComponentIntervalEdges_subset_range P C hj)
  have hjlt' : j < 2 * slack P := by simpa [hdouble] using hjlt
  let k := j / 2
  have hk : k < slack P := by
    have hmod := Nat.mod_add_div j 2
    have hmodlt : j % 2 < 2 := Nat.mod_lt _ (by omega)
    simp only [k]
    omega
  obtain ⟨Ck, hCk⟩ := htiles k hk
  have hjCk : j ∈ offCorridorComponentIntervalEdges P Ck := by
    rw [hCk]
    have hmod := Nat.mod_add_div j 2
    have hmodlt : j % 2 < 2 := Nat.mod_lt _ (by omega)
    simp only [Finset.mem_Ico]
    simp only [k]
    omega
  have hCCk : C = Ck := by
    by_contra hne
    have hd := hdisjoint (by simp) (by simp) hne
    exact (Finset.disjoint_left.mp hd hj hjCk).elim
  exact ⟨k, hk, by simpa [hCCk] using hCk⟩

/-- The component occupying an even tile has a unique vertex, and that
vertex is adjacent to both articulation endpoints of the tile. -/
theorem IsGeodesic.exists_tileVertex_adj_endpoints
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ : V} {P : G.Walk w x₀}
    (hP : IsGeodesic P) (hdouble : P.length = 2 * slack P)
    (hnonbridge : ∀ i < P.length,
      ¬G.IsBridge s(P.getVert i, P.getVert (i + 1)))
    {k : ℕ} (hk : k < slack P) :
    ∃ C : OffCorridorComponent P, ∃ c : V,
      offCorridorComponentFinset C = {c} ∧
      offCorridorComponentIntervalEdges P C =
        Finset.Ico (2 * k) (2 * k + 2) ∧
      G.Adj c (P.getVert (2 * k)) ∧
      G.Adj c (P.getVert (2 * k + 2)) := by
  classical
  obtain ⟨htiles, _hdisjoint, hunit⟩ :=
    Erdos23GapGBJoint.IsGeodesic.doubleSlack_allNonbridge_rigidity
      hP hdouble hnonbridge
  obtain ⟨C, hCtile⟩ := htiles k hk
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (hunit C).1
  obtain ⟨hleft, hright, _hbounds⟩ :=
    attachment_extrema_of_interval_eq_two P C (2 * k) (by
      simpa [Nat.add_assoc] using hCtile)
  obtain ⟨_hlength, cL, hcL, hAdjL⟩ :=
    (mem_offCorridorAttachmentIndices P C (2 * k)).1 hleft
  obtain ⟨_hrlength, cR, hcR, hAdjR⟩ :=
    (mem_offCorridorAttachmentIndices P C (2 * k + 2)).1 hright
  have hcL' : cL = c := by simpa [hc] using hcL
  have hcR' : cR = c := by simpa [hc] using hcR
  subst cL
  subst cR
  exact ⟨C, c, hc, hCtile, hAdjL, hAdjR⟩

/-- A vertex projection to the chain of even articulations.  The projection
records exactly which internal block-boundary cuts contain the vertex. -/
structure BoundaryProjection
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ : V} (P : G.Walk w x₀) (x : V) where
  block : ℕ
  block_le : block ≤ slack P
  anchor_dist : G.dist x (P.getVert (2 * block)) ≤ 1
  mem_cut : ∀ k : Fin (slack P - 1),
    (x ∈ boundaryLeftCut P k.1 ↔ block < k.1 + 1)
  terminal_eq : block = slack P → x = P.getVert (2 * slack P)

/-- Equality rigidity supplies a boundary projection for every graph
vertex.  On-corridor vertices use their coordinate divided by two; an
off-corridor vertex uses the left endpoint of its unique even tile. -/
theorem IsGeodesic.exists_boundaryProjection
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ x : V} {P : G.Walk w x₀}
    (hP : IsGeodesic P) (hdouble : P.length = 2 * slack P)
    (hnonbridge : ∀ i < P.length,
      ¬G.IsBridge s(P.getVert i, P.getVert (i + 1))) :
    Nonempty (BoundaryProjection P x) := by
  classical
  by_cases hx : x ∈ P.support
  · let j := P.support.idxOf x
    have hjle : j ≤ P.length := support_idxOf_le_length P hx
    have hget : P.getVert j = x := P.getVert_support_idxOf hx
    have hmod := Nat.mod_add_div j 2
    have hmodlt : j % 2 < 2 := Nat.mod_lt _ (by omega)
    have hblockLe : j / 2 ≤ slack P := by
      rw [hdouble] at hjle
      omega
    have hanchorLe : 2 * (j / 2) ≤ j := by omega
    have hanchorDist : G.dist x (P.getVert (2 * (j / 2))) ≤ 1 := by
      have hd := hP.dist_getVert_eq_sub hanchorLe hjle
      rw [hget] at hd
      rw [dist_comm, hd]
      omega
    refine ⟨{
      block := j / 2
      block_le := hblockLe
      anchor_dist := hanchorDist
      mem_cut := ?_
      terminal_eq := ?_ }⟩
    · intro k
      rw [mem_boundaryLeftCut,
        mem_corridorLeftRegion_of_mem_support P (2 * k.1 + 1) hx]
      change (j ≤ 2 * k.1 + 1 ↔ j / 2 < k.1 + 1)
      omega
    · intro hterminal
      have hj : j = 2 * slack P := by
        rw [hdouble] at hjle
        omega
      rw [← hget, hj]
  · let C := offCorridorComponentOf P x hx
    obtain ⟨k, hk, htile⟩ :=
      Erdos23GapGBEqualityBoundary.IsGeodesic.every_offCorridorComponent_is_even_tile
        hP hdouble hnonbridge C
    obtain ⟨_htiles, _hdisjoint, hunit⟩ :=
      Erdos23GapGBJoint.IsGeodesic.doubleSlack_allNonbridge_rigidity
        hP hdouble hnonbridge
    have hxC : x ∈ offCorridorComponentFinset C := by
      simpa [C] using mem_offCorridorComponentOf P hx
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (hunit C).1
    have hxc : x = c := by simpa [hc] using hxC
    have hcset : offCorridorComponentFinset C = {x} := by simpa [hxc] using hc
    obtain ⟨hleft, _hright, hbounds⟩ :=
      attachment_extrema_of_interval_eq_two P C (2 * k) (by
        simpa [Nat.add_assoc] using htile)
    obtain ⟨_hlen, cL, hcL, hAdjL⟩ :=
      (mem_offCorridorAttachmentIndices P C (2 * k)).1 hleft
    have hcLx : cL = x := by simpa [hcset] using hcL
    subst cL
    refine ⟨{
      block := k
      block_le := hk.le
      anchor_dist := by
        rw [dist_eq_one_iff_adj.mpr hAdjL]
      mem_cut := ?_
      terminal_eq := by intro; omega }⟩
    intro t
    rw [mem_boundaryLeftCut,
      mem_corridorLeftRegion_of_not_mem_support P (2 * t.1 + 1) hx]
    constructor
    · rintro ⟨j, hjA, hjle⟩
      have hjbounds := hbounds j hjA
      omega
    · intro hkt
      exact ⟨2 * k, hleft, by omega⟩

/-- Even articulation coordinates realize twice the distance of their block
indices along the geodesic. -/
theorem IsGeodesic.dist_even_anchors
    {V : Type*} {G : SimpleGraph V} {w x₀ : V} {P : G.Walk w x₀}
    (hP : IsGeodesic P) {s a b : ℕ} (hdouble : P.length = 2 * s)
    (ha : a ≤ s) (hb : b ≤ s) :
    G.dist (P.getVert (2 * a)) (P.getVert (2 * b)) = 2 * Nat.dist a b := by
  rcases le_total a b with hab | hba
  · rw [hP.dist_getVert_eq_sub (by omega) (by omega),
      Nat.dist_eq_sub_of_le hab]
    omega
  · rw [dist_comm, hP.dist_getVert_eq_sub (by omega) (by omega),
      Nat.dist_eq_sub_of_le_right hba]
    omega

@[simp]
theorem separationDemand_eq_separation_membership
    {V : Type*} [DecidableEq V] (T : Finset V) (x y : V) :
    separationDemand T x y =
      separation (decide (x ∈ T)) (decide (y ∈ T)) := by
  by_cases hx : x ∈ T <;> by_cases hy : y ∈ T <;>
    simp [separationDemand, separation, hx, hy]

/-- The exact graph input required by the articulation-cut arithmetic:
every even-distance demand is at most twice the number of internal boundary
cuts it crosses, plus two. -/
theorem IsGeodesic.dist_le_twice_sum_boundaryCuts_add_two
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ x y : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P)
    (hdouble : P.length = 2 * slack P)
    (hnonbridge : ∀ i < P.length,
      ¬G.IsBridge s(P.getVert i, P.getVert (i + 1)))
    (heven : Even (G.dist x y)) :
    G.dist x y ≤ 2 *
      (∑ k : Fin (slack P - 1),
        separationDemand (boundaryLeftCut P k.1) x y) + 2 := by
  classical
  let px := Classical.choice
    (Erdos23GapGBEqualityBoundary.IsGeodesic.exists_boundaryProjection
      hP hdouble hnonbridge (x := x))
  let py := Classical.choice
    (Erdos23GapGBEqualityBoundary.IsGeodesic.exists_boundaryProjection
      hP hdouble hnonbridge (x := y))
  let a := px.block
  let b := py.block
  have ha : a ≤ slack P := px.block_le
  have hb : b ≤ slack P := py.block_le
  have hsum :
      (∑ k : Fin (slack P - 1),
        separationDemand (boundaryLeftCut P k.1) x y) =
      ∑ k : Fin (slack P - 1),
        separation (decide (a < k.1 + 1)) (decide (b < k.1 + 1)) := by
    apply Finset.sum_congr rfl
    intro k _
    have hxiff : x ∈ boundaryLeftCut P k.1 ↔ a < k.1 + 1 := by
      simpa [a] using px.mem_cut k
    have hyiff : y ∈ boundaryLeftCut P k.1 ↔ b < k.1 + 1 := by
      simpa [b] using py.mem_cut k
    rw [separationDemand_eq_separation_membership]
    by_cases hxmem : x ∈ boundaryLeftCut P k.1 <;>
      by_cases hymem : y ∈ boundaryLeftCut P k.1 <;>
      simp [separation, hxmem, hymem] at * <;> omega
  have hanchor :
      G.dist (P.getVert (2 * a)) (P.getVert (2 * b)) =
        2 * Nat.dist a b := by
    exact Erdos23GapGBEqualityBoundary.IsGeodesic.dist_even_anchors
      hP hdouble ha hb
  have hyAnchor : G.dist (P.getVert (2 * b)) y ≤ 1 := by
    rw [SimpleGraph.dist_comm]
    exact py.anchor_dist
  have hxAnchor : G.dist x (P.getVert (2 * a)) ≤ 1 := px.anchor_dist
  have htri₁ : G.dist x y ≤
      G.dist x (P.getVert (2 * a)) +
        G.dist (P.getVert (2 * a)) y := hconn.dist_triangle
  have htri₂ : G.dist (P.getVert (2 * a)) y ≤
      G.dist (P.getVert (2 * a)) (P.getVert (2 * b)) +
        G.dist (P.getVert (2 * b)) y := hconn.dist_triangle
  by_cases hat : a < slack P
  · by_cases hbt : b < slack P
    · have hcoord := blockCoordinate_boundarySeparation_eq_dist_of_lt hat hbt
      rw [← hsum] at hcoord
      omega
    · have hbeq : b = slack P := by omega
      have hyEq := py.terminal_eq hbeq
      have hyZero : G.dist (P.getVert (2 * b)) y = 0 := by
        rw [hbeq, hyEq]
        simp
      have hcoord := blockCoordinate_dist_le_boundarySeparation_add_one ha hb
      rw [← hsum] at hcoord
      rcases heven with ⟨q, hq⟩
      omega
  · have haeq : a = slack P := by omega
    have hxEq := px.terminal_eq haeq
    have hxZero : G.dist x (P.getVert (2 * a)) = 0 := by
      rw [haeq, hxEq]
      simp
    by_cases hbt : b < slack P
    · have hcoord := blockCoordinate_dist_le_boundarySeparation_add_one ha hb
      rw [← hsum] at hcoord
      rcases heven with ⟨q, hq⟩
      omega
    · have hbeq : b = slack P := by omega
      have hcoordZero : Nat.dist a b = 0 := by simp [haeq, hbeq]
      rw [hcoordZero] at hanchor
      omega

/-- At an internal even articulation, every oriented graph edge leaving the
left boundary cut is one of the two edges entering that articulation: the
corridor edge or the detour edge from the unique tile vertex. -/
theorem IsGeodesic.exists_boundaryCrossing_classifier
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    (hP : IsGeodesic P) (hdouble : P.length = 2 * slack P)
    (hnonbridge : ∀ i < P.length,
      ¬G.IsBridge s(P.getVert i, P.getVert (i + 1)))
    {k : ℕ} (hk : k < slack P - 1) :
    ∃ c : V, ∀ {a b : V},
      a ∈ boundaryLeftCut P k → b ∉ boundaryLeftCut P k → G.Adj a b →
      (a = P.getVert (2 * k + 1) ∧ b = P.getVert (2 * k + 2)) ∨
      (a = c ∧ b = P.getVert (2 * k + 2)) := by
  classical
  have hks : k < slack P := by omega
  obtain ⟨C, c, hCset, hCtile, _hAdjLeft, _hAdjRight⟩ :=
    Erdos23GapGBEqualityBoundary.IsGeodesic.exists_tileVertex_adj_endpoints
      hP hdouble hnonbridge hks
  obtain ⟨_htiles, hdisjoint, _hunit⟩ :=
    Erdos23GapGBJoint.IsGeodesic.doubleSlack_allNonbridge_rigidity
      hP hdouble hnonbridge
  obtain ⟨_hleft, _hright, hbounds⟩ :=
    attachment_extrema_of_interval_eq_two P C (2 * k) (by
      simpa [Nat.add_assoc] using hCtile)
  refine ⟨c, ?_⟩
  intro a b ha hb hab
  have haLeft : a ∈ corridorLeftRegion P (2 * k + 1) :=
    (mem_boundaryLeftCut P k).1 ha
  have hbRight : b ∉ corridorLeftRegion P (2 * k + 1) := by
    simpa [mem_boundaryLeftCut] using hb
  by_cases haP : a ∈ P.support
  · have hai : P.support.idxOf a ≤ 2 * k + 1 :=
      (mem_corridorLeftRegion_of_mem_support P (2 * k + 1) haP).1 haLeft
    by_cases hbP : b ∈ P.support
    · have hib : 2 * k + 1 < P.support.idxOf b := by
        by_contra hnot
        exact hbRight
          ((mem_corridorLeftRegion_of_mem_support P (2 * k + 1) hbP).2
            (by omega))
      have hdist : Nat.dist (P.support.idxOf a) (P.support.idxOf b) = 1 := by
        rw [← hP.dist_eq_natDist_support_idxOf haP hbP]
        exact dist_eq_one_iff_adj.mpr hab
      have hsucc : P.support.idxOf b = P.support.idxOf a + 1 := by
        unfold Nat.dist at hdist
        omega
      have haidx : P.support.idxOf a = 2 * k + 1 := by omega
      have hbidx : P.support.idxOf b = 2 * k + 2 := by omega
      left
      constructor
      · calc
          a = P.getVert (P.support.idxOf a) :=
            (P.getVert_support_idxOf haP).symm
          _ = P.getVert (2 * k + 1) := by rw [haidx]
      · calc
          b = P.getVert (P.support.idxOf b) :=
            (P.getVert_support_idxOf hbP).symm
          _ = P.getVert (2 * k + 2) := by rw [hbidx]
    · have haGet : P.getVert (P.support.idxOf a) = a :=
        P.getVert_support_idxOf haP
      have haIdxLe : P.support.idxOf a ≤ P.length :=
        support_idxOf_le_length P haP
      have hatt : P.support.idxOf a ∈
          offCorridorAttachmentIndices P (offCorridorComponentOf P b hbP) := by
        apply attachment_mem_of_offCorridor_adj P hbP haIdxLe
        simpa [haGet] using hab.symm
      have hbLeft : b ∈ corridorLeftRegion P (2 * k + 1) :=
        (mem_corridorLeftRegion_of_not_mem_support P (2 * k + 1) hbP).2
          ⟨P.support.idxOf a, hatt, hai⟩
      exact (hbRight hbLeft).elim

  · obtain ⟨j, hjatt, hji⟩ :=
      (mem_corridorLeftRegion_of_not_mem_support P (2 * k + 1) haP).1 haLeft
    by_cases hbP : b ∈ P.support
    · have hib : 2 * k + 1 < P.support.idxOf b := by
        by_contra hnot
        exact hbRight
          ((mem_corridorLeftRegion_of_mem_support P (2 * k + 1) hbP).2
            (by omega))
      have hbIdxLe : P.support.idxOf b ≤ P.length :=
        support_idxOf_le_length P hbP
      have hbGet : P.getVert (P.support.idxOf b) = b :=
        P.getVert_support_idxOf hbP
      let Ca := offCorridorComponentOf P a haP
      have hbatt : P.support.idxOf b ∈ offCorridorAttachmentIndices P Ca := by
        apply attachment_mem_of_offCorridor_adj P haP hbIdxLe
        simpa [hbGet] using hab
      have hcover : offCorridorComponentCoversIndex P Ca (2 * k + 1) :=
        ⟨j, by simpa [Ca] using hjatt,
          P.support.idxOf b, hbatt, hji, by omega⟩
      have hiCa : 2 * k + 1 ∈ offCorridorComponentIntervalEdges P Ca :=
        mem_offCorridorComponentIntervalEdges_of_coversIndex P Ca hcover
      have hiC : 2 * k + 1 ∈ offCorridorComponentIntervalEdges P C := by
        rw [hCtile]
        simp
      have hCaC : Ca = C := by
        by_contra hne
        have hd := hdisjoint (by simp) (by simp) hne
        exact (Finset.disjoint_left.mp hd hiCa hiC).elim
      have haC : a ∈ offCorridorComponentFinset C := by
        have haOwn : a ∈ offCorridorComponentFinset Ca := by
          simpa [Ca] using mem_offCorridorComponentOf P haP
        simpa [hCaC] using haOwn
      have hac : a = c := by simpa [hCset] using haC
      have hbattC : P.support.idxOf b ∈ offCorridorAttachmentIndices P C := by
        simpa [hCaC] using hbatt
      have hbBounds := hbounds (P.support.idxOf b) hbattC
      have hbidx : P.support.idxOf b = 2 * k + 2 := by omega
      right
      exact ⟨hac, by
        calc
          b = P.getVert (P.support.idxOf b) :=
            (P.getVert_support_idxOf hbP).symm
          _ = P.getVert (2 * k + 2) := by rw [hbidx]⟩
    · have hcomp := offCorridorComponentOf_eq_of_adj P haP hbP hab
      have hbLeft : b ∈ corridorLeftRegion P (2 * k + 1) :=
        (mem_corridorLeftRegion_of_not_mem_support P (2 * k + 1) hbP).2
          ⟨j, by simpa [hcomp] using hjatt, hji⟩
      exact (hbRight hbLeft).elim

/-- Each internal boundary cut has graph capacity at most two. -/
theorem IsGeodesic.cutSize_boundaryLeftCut_le_two
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    (hP : IsGeodesic P) (hdouble : P.length = 2 * slack P)
    (hnonbridge : ∀ i < P.length,
      ¬G.IsBridge s(P.getVert i, P.getVert (i + 1)))
    {k : ℕ} (hk : k < slack P - 1) :
    cutSize G (boundaryLeftCut P k) ≤ 2 := by
  classical
  obtain ⟨c, hclass⟩ :=
    Erdos23GapGBEqualityBoundary.IsGeodesic.exists_boundaryCrossing_classifier
      hP hdouble hnonbridge hk
  let crossingPairs := (boundaryLeftCut P k).sigma fun a =>
    G.neighborFinset a \ boundaryLeftCut P k
  let allowed : Finset (Sigma fun _ : V => V) :=
    {⟨P.getVert (2 * k + 1), P.getVert (2 * k + 2)⟩,
      ⟨c, P.getVert (2 * k + 2)⟩}
  have hsubset : crossingPairs ⊆ allowed := by
    intro e he
    obtain ⟨a, b⟩ := e
    have heData : a ∈ boundaryLeftCut P k ∧
        b ∈ G.neighborFinset a \ boundaryLeftCut P k := by
      simpa [crossingPairs] using he
    have hbData : G.Adj a b ∧ b ∉ boundaryLeftCut P k := by
      simpa using heData.2
    rcases hclass heData.1 hbData.2 hbData.1 with hpath | hoff
    · simp [allowed, hpath.1, hpath.2]
    · simp [allowed, hoff.1, hoff.2]
  calc
    cutSize G (boundaryLeftCut P k) = crossingPairs.card := by
      simp [cutSize, crossingPairs, Finset.card_sigma]
    _ ≤ allowed.card := Finset.card_le_card hsubset
    _ ≤ 2 := Finset.card_le_two

@[simp]
theorem separationDemand_univ_sdiff
    {V : Type*} [Fintype V] [DecidableEq V]
    (T : Finset V) (x y : V) :
    separationDemand (Finset.univ \ T) x y = separationDemand T x y := by
  by_cases hx : x ∈ T <;> by_cases hy : y ∈ T <;>
    simp [separationDemand, hx, hy]

/-- A finite graph cut and its complement have the same number of crossing
edges. -/
theorem cutSize_univ_sdiff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) :
    cutSize G (Finset.univ \ T) = cutSize G T := by
  classical
  let Tc := Finset.univ \ T
  let cross (S : Finset V) := S.sigma fun a => G.neighborFinset a \ S
  have hcard : (cross Tc).card = (cross T).card := by
    refine Finset.card_bij'
      (fun e _ => ⟨e.2, e.1⟩) (fun e _ => ⟨e.2, e.1⟩)
      ?_ ?_ ?_ ?_
    · intro e he
      obtain ⟨a, b⟩ := e
      have heData : a ∈ Tc ∧ b ∈ G.neighborFinset a \ Tc := by
        simpa [cross] using he
      have haT : a ∉ T := by simpa [Tc] using heData.1
      have hbData : G.Adj a b ∧ b ∉ Tc := by simpa using heData.2
      have hbT : b ∈ T := by simpa [Tc] using hbData.2
      simp [cross, hbT, haT, hbData.1.symm]
    · intro e he
      obtain ⟨a, b⟩ := e
      have heData : a ∈ T ∧ b ∈ G.neighborFinset a \ T := by
        simpa [cross] using he
      have hbData : G.Adj a b ∧ b ∉ T := by simpa using heData.2
      have hbTc : b ∈ Tc := by simpa [Tc] using hbData.2
      have haNotTc : a ∉ Tc := by simpa [Tc] using heData.1
      simp [cross, hbTc, haNotTc, hbData.1.symm]
    · intro e he
      rcases e with ⟨a, b⟩
      rfl
    · intro e he
      rcases e with ⟨a, b⟩
      rfl
  simpa [cutSize, cross, Tc, Finset.card_sigma] using hcard

/-- The root-excluding RFC is equivalent to its symmetric all-cuts form. -/
theorem symmetricRootedCutCondition_of_rootForm
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m₁ m₂ : I → V) (w x₀ : V)
    (hRFC : ∀ T : Finset V, w ∉ T →
      (∑ i : I, separationDemand T (m₁ i) (m₂ i)) +
        (if x₀ ∈ T then 1 else 0) ≤ cutSize G T) :
    ∀ T : Finset V,
      (∑ i : I, separationDemand T (m₁ i) (m₂ i)) +
        separationDemand T w x₀ ≤ cutSize G T := by
  classical
  intro T
  by_cases hw : w ∈ T
  · let Tc := Finset.univ \ T
    have hwc : w ∉ Tc := by simpa [Tc] using hw
    have h := hRFC Tc hwc
    have hdemands : (∑ i : I, separationDemand Tc (m₁ i) (m₂ i)) =
        ∑ i : I, separationDemand T (m₁ i) (m₂ i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp [Tc]
    have hstub : (if x₀ ∈ Tc then 1 else 0) =
        separationDemand T w x₀ := by
      by_cases hx : x₀ ∈ T <;> simp [Tc, separationDemand, hw, hx]
    rw [hdemands, hstub, cutSize_univ_sdiff G T] at h
    exact h
  · have h := hRFC T hw
    have hstub : (if x₀ ∈ T then 1 else 0) =
        separationDemand T w x₀ := by
      by_cases hx : x₀ ∈ T <;> simp [separationDemand, hw, hx]
    simpa [hstub] using h

/-- Every internal boundary cut separates the root from the stub terminal. -/
theorem IsGeodesic.separationDemand_boundaryLeftCut_terminals_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ : V} {P : G.Walk w x₀}
    (hP : IsGeodesic P) (hdouble : P.length = 2 * slack P)
    (k : Fin (slack P - 1)) :
    separationDemand (boundaryLeftCut P k.1) w x₀ = 1 := by
  classical
  have hk : k.1 < slack P - 1 := k.2
  have hi : 2 * k.1 + 1 < P.length := by
    rw [hdouble]
    omega
  have hw : w ∈ boundaryLeftCut P k.1 := by
    rw [mem_boundaryLeftCut]
    simpa using hP.getVert_mem_corridorLeftRegion
      (i := 2 * k.1 + 1) (j := 0) (by omega) (by omega)
  have hx₀ : x₀ ∉ boundaryLeftCut P k.1 := by
    rw [mem_boundaryLeftCut]
    simpa using hP.getVert_not_mem_corridorLeftRegion
      (i := 2 * k.1 + 1) (j := P.length) (by omega) hi
  simp [separationDemand, hw, hx₀]

/-- Complete unconditional closure of the bridge-free `d = 2s` slice of
BF-RL.  The internal demands satisfy the symmetric rooted cut condition,
have legal distance at least four, and have even distance (the bipartite
same-side condition). -/
theorem totalCost_le_rlBudget_of_doubleSlack_allNonbridge
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀} (m₁ m₂ : I → V)
    (hconn : G.Connected) (hP : IsGeodesic P)
    (hdouble : P.length = 2 * slack P)
    (hnonbridge : ∀ i < P.length,
      ¬G.IsBridge s(P.getVert i, P.getVert (i + 1)))
    (hRFC : ∀ T : Finset V,
      (∑ i : I, separationDemand T (m₁ i) (m₂ i)) +
        separationDemand T w x₀ ≤ cutSize G T)
    (hs : 5 ≤ slack P)
    (hlegal : ∀ i, 4 ≤ G.dist (m₁ i) (m₂ i))
    (heven : ∀ i, Even (G.dist (m₁ i) (m₂ i))) :
    (∑ i : I, (G.dist (m₁ i) (m₂ i) + 1) ^ 2) ≤
      rlBudget (slack P) (2 * slack P) := by
  classical
  apply totalCost_le_doubleSlackBudget_of_articulationCuts
    (I := I) (K := Fin (slack P - 1))
    (fun i => G.dist (m₁ i) (m₂ i))
    (fun i k => separationDemand (boundaryLeftCut P k.1) (m₁ i) (m₂ i))
    (slack P) hs
  · simp
  · exact hlegal
  · intro k
    have hcut := hRFC (boundaryLeftCut P k.1)
    have hterminal :=
      IsGeodesic.separationDemand_boundaryLeftCut_terminals_eq_one
        hP hdouble k
    have hsize :=
      IsGeodesic.cutSize_boundaryLeftCut_le_two
        hP hdouble hnonbridge k.2
    omega
  · intro i
    exact IsGeodesic.dist_le_twice_sum_boundaryCuts_add_two
        hconn hP hdouble hnonbridge (heven i)

/-- Root-excluding RFC form of the equality-boundary closure, matching the
original one-stub definition literally. -/
theorem totalCost_le_rlBudget_of_doubleSlack_allNonbridge_rootForm
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀} (m₁ m₂ : I → V)
    (hconn : G.Connected) (hP : IsGeodesic P)
    (hdouble : P.length = 2 * slack P)
    (hnonbridge : ∀ i < P.length,
      ¬G.IsBridge s(P.getVert i, P.getVert (i + 1)))
    (hRFC : ∀ T : Finset V, w ∉ T →
      (∑ i : I, separationDemand T (m₁ i) (m₂ i)) +
        (if x₀ ∈ T then 1 else 0) ≤ cutSize G T)
    (hs : 5 ≤ slack P)
    (hlegal : ∀ i, 4 ≤ G.dist (m₁ i) (m₂ i))
    (heven : ∀ i, Even (G.dist (m₁ i) (m₂ i))) :
    (∑ i : I, (G.dist (m₁ i) (m₂ i) + 1) ^ 2) ≤
      rlBudget (slack P) (2 * slack P) := by
  exact totalCost_le_rlBudget_of_doubleSlack_allNonbridge
    m₁ m₂ hconn hP hdouble hnonbridge
    (symmetricRootedCutCondition_of_rootForm G m₁ m₂ w x₀ hRFC)
    hs hlegal heven

/-- Two vertices assigned the same side by a Boolean graph coloring have
even graph distance in a connected graph. -/
theorem Coloring.even_dist_of_eq
    {V : Type*} {G : SimpleGraph V} (hconn : G.Connected)
    (color : G.Coloring Bool) {x y : V} (hsame : color x = color y) :
    Even (G.dist x y) := by
  obtain ⟨Q, hQ⟩ := hconn.exists_walk_length_eq_dist x y
  rw [← hQ]
  apply (color.even_length_iff_congr Q).2
  rw [hsame]

/-- Same-side form of the root-RFC theorem.  This is the literal
bipartite-instance interface: parity is derived rather than assumed. -/
theorem totalCost_le_rlBudget_of_doubleSlack_allNonbridge_sameSide
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀} (m₁ m₂ : I → V)
    (hconn : G.Connected) (color : G.Coloring Bool)
    (hP : IsGeodesic P) (hdouble : P.length = 2 * slack P)
    (hnonbridge : ∀ i < P.length,
      ¬G.IsBridge s(P.getVert i, P.getVert (i + 1)))
    (hRFC : ∀ T : Finset V, w ∉ T →
      (∑ i : I, separationDemand T (m₁ i) (m₂ i)) +
        (if x₀ ∈ T then 1 else 0) ≤ cutSize G T)
    (hs : 5 ≤ slack P)
    (hlegal : ∀ i, 4 ≤ G.dist (m₁ i) (m₂ i))
    (hsame : ∀ i, color (m₁ i) = color (m₂ i)) :
    (∑ i : I, (G.dist (m₁ i) (m₂ i) + 1) ^ 2) ≤
      rlBudget (slack P) (2 * slack P) := by
  apply totalCost_le_rlBudget_of_doubleSlack_allNonbridge_rootForm
    m₁ m₂ hconn hP hdouble hnonbridge hRFC hs hlegal
  intro i
  exact Coloring.even_dist_of_eq hconn color (hsame i)

#print axioms blockCoordinate_dist_le_boundarySeparation_add_one
#print axioms attachment_extrema_of_interval_eq_two
#print axioms IsGeodesic.every_offCorridorComponent_is_even_tile
#print axioms IsGeodesic.exists_tileVertex_adj_endpoints
#print axioms IsGeodesic.exists_boundaryProjection
#print axioms IsGeodesic.dist_even_anchors
#print axioms IsGeodesic.dist_le_twice_sum_boundaryCuts_add_two
#print axioms IsGeodesic.exists_boundaryCrossing_classifier
#print axioms IsGeodesic.cutSize_boundaryLeftCut_le_two
#print axioms IsGeodesic.separationDemand_boundaryLeftCut_terminals_eq_one
#print axioms cutSize_univ_sdiff
#print axioms symmetricRootedCutCondition_of_rootForm
#print axioms totalCost_le_rlBudget_of_doubleSlack_allNonbridge
#print axioms totalCost_le_rlBudget_of_doubleSlack_allNonbridge_rootForm
#print axioms Coloring.even_dist_of_eq
#print axioms totalCost_le_rlBudget_of_doubleSlack_allNonbridge_sameSide

end Erdos23GapGBEqualityBoundary
