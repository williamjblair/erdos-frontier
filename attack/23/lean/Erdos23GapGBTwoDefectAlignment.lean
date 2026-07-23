/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair, OpenAI Codex
-/
import ErdosProblems.Erdos23GapGBTwoDefect
import ErdosProblems.Erdos23GapGBOneDefectAlignment

/-!
# Erdős 23 G-B: graph alignment on the two-defect boundary

This module turns the five abstract `d = 2s-2` component shapes into their
literal BFS geometries.  It is intentionally separate from the defect and
matrix arithmetic in `Erdos23GapGBTwoDefect`.
-/

namespace Erdos23GapGBTwoDefectAlignment

open scoped BigOperators
open SimpleGraph
open Erdos23GapGA
open Erdos23GapGBSeries
open Erdos23GapGBJoint
open Erdos23GapGBEqualityBoundary
open Erdos23GapGBOneDefect
open Erdos23GapGBOneDefectAlignment
open Erdos23GapGBOneDefectIntervals
open Erdos23GapGBBinaryLayers
open Erdos23GapGBLayerCapacity
open Erdos23GapGBTwoDefect

/-- An interval identity of arbitrary positive length determines both
extreme attachments and bounds every other attachment between them. -/
theorem attachment_extrema_of_interval_eq_length
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ : V} (P : G.Walk w x₀)
    (C : OffCorridorComponent P) (l h : ℕ) (hpos : 1 ≤ h)
    (hinterval : offCorridorComponentIntervalEdges P C =
      Finset.Ico l (l + h)) :
    l ∈ offCorridorAttachmentIndices P C ∧
      l + h ∈ offCorridorAttachmentIndices P C ∧
      ∀ j ∈ offCorridorAttachmentIndices P C, l ≤ j ∧ j ≤ l + h := by
  classical
  let A := offCorridorAttachmentIndices P C
  have hnonempty : (offCorridorComponentIntervalEdges P C).Nonempty := by
    rw [hinterval]
    exact ⟨l, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩⟩
  have hA : A.Nonempty := by
    by_contra hempty
    have : offCorridorComponentIntervalEdges P C = ∅ := by
      simp [offCorridorComponentIntervalEdges, A, hempty]
    rw [this] at hnonempty
    exact Finset.not_nonempty_empty hnonempty
  have hdef : offCorridorComponentIntervalEdges P C =
      Finset.Ico (A.min' hA) (A.max' hA) := by
    simp [offCorridorComponentIntervalEdges, A, hA]
  have hcard : (Finset.Ico (A.min' hA) (A.max' hA)).card = h := by
    rw [← hdef, hinterval]
    simp
  have hdiff : A.max' hA - A.min' hA = h := by
    simpa [Nat.card_Ico] using hcard
  have hlmem : l ∈ Finset.Ico (A.min' hA) (A.max' hA) := by
    rw [← hdef, hinterval]
    exact Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
  have hlastmem : l + h - 1 ∈
      Finset.Ico (A.min' hA) (A.max' hA) := by
    rw [← hdef, hinterval]
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hmin : A.min' hA = l := by
    have hl := Finset.mem_Ico.mp hlmem
    have hlast := Finset.mem_Ico.mp hlastmem
    omega
  have hmax : A.max' hA = l + h := by omega
  constructor
  · simpa [A, hmin] using A.min'_mem hA
  constructor
  · simpa [A, hmax] using A.max'_mem hA
  · intro j hj
    have hjA : j ∈ A := by simpa [A] using hj
    have hminLe := A.min'_le j hjA
    have hleMax := A.le_max' j hjA
    omega

/-- Two vertices of one canonical off-corridor component are joined by a
simple graph path whose whole support remains in that component. -/
theorem exists_isPath_support_subset_offCorridorComponent
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ x y : V} {P : G.Walk w x₀}
    (C : OffCorridorComponent P)
    (hx : x ∈ offCorridorComponentFinset C)
    (hy : y ∈ offCorridorComponentFinset C) :
    ∃ W : G.Walk x y, W.IsPath ∧
      ∀ z ∈ W.support, z ∈ offCorridorComponentFinset C := by
  classical
  have hxC : x ∈ C := (mem_offCorridorComponentFinset C).1 hx
  have hyC : y ∈ C := (mem_offCorridorComponentFinset C).1 hy
  obtain ⟨hxOff, hxEq⟩ := ComponentCompl.mem_supp_iff.mp hxC
  obtain ⟨hyOff, hyEq⟩ := ComponentCompl.mem_supp_iff.mp hyC
  let x' : {a : V // a ∉ (supportFinset P : Set V)} := ⟨x, hxOff⟩
  let y' : {a : V // a ∉ (supportFinset P : Set V)} := ⟨y, hyOff⟩
  have hx' : x' ∈ ConnectedComponent.supp C :=
    (ConnectedComponent.mem_supp_iff C x').2 hxEq
  have hy' : y' ∈ ConnectedComponent.supp C :=
    (ConnectedComponent.mem_supp_iff C y').2 hyEq
  obtain ⟨W, hW⟩ :=
    C.connected_toSimpleGraph.exists_isPath ⟨x', hx'⟩ ⟨y', hy'⟩
  let Woff := W.map C.toSimpleGraph_hom
  let W' : G.Walk x y :=
    (Woff.map (Embedding.induce (supportFinset P : Set V)ᶜ).toHom).copy rfl rfl
  have hWoff : Woff.IsPath :=
    Walk.map_isPath_of_injective Subtype.val_injective hW
  have hW' : W'.IsPath := by
    simpa [W'] using Walk.map_isPath_of_injective Subtype.val_injective hWoff
  refine ⟨W', hW', ?_⟩
  intro z hz
  change z ∈
    ((Woff.map (Embedding.induce (supportFinset P : Set V)ᶜ).toHom).copy
      rfl rfl).support at hz
  simp only [Walk.support_copy, Walk.support_map] at hz
  obtain ⟨zOff, hzOff, rfl⟩ := List.mem_map.mp hz
  change zOff ∈ (W.map C.toSimpleGraph_hom).support at hzOff
  rw [Walk.support_map] at hzOff
  obtain ⟨zC, _, hzC⟩ := List.mem_map.mp hzOff
  have hval : zOff = zC.val := by simpa using hzC.symm
  rw [hval]
  have hcomp : G.componentComplMk zC.val.prop = C :=
    (ConnectedComponent.mem_supp_iff C zC.val).1 zC.prop
  exact (mem_offCorridorComponentFinset C).2
    (ComponentCompl.mem_supp_iff.mpr ⟨zC.val.prop, hcomp⟩)

/-- Every vertex of an off-corridor component is placed on the left of a
boundary once that component has an attachment on the left. -/
theorem mem_corridorLeftRegion_of_mem_offCorridorComponent
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ x : V} {P : G.Walk w x₀}
    (C : OffCorridorComponent P)
    (hx : x ∈ offCorridorComponentFinset C)
    {i j : ℕ} (hj : j ∈ offCorridorAttachmentIndices P C)
    (hji : j ≤ i) :
    x ∈ corridorLeftRegion P i := by
  have hxComp : x ∈ C := (mem_offCorridorComponentFinset C).1 hx
  obtain ⟨hxOff, hxEq⟩ := ComponentCompl.mem_supp_iff.mp hxComp
  have hxNot : x ∉ P.support := by simpa [supportFinset] using hxOff
  apply (mem_corridorLeftRegion_of_not_mem_support P i hxNot).2
  refine ⟨j, ?_, hji⟩
  have hcomponent : offCorridorComponentOf P x hxNot = C := by
    simpa [offCorridorComponentOf, supportFinset] using hxEq
  rw [hcomponent]
  exact hj

theorem mem_offCorridorFinset_of_mem_componentFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ x : V} {P : G.Walk w x₀}
    {C : OffCorridorComponent P}
    (hx : x ∈ offCorridorComponentFinset C) :
    x ∈ offCorridorFinset P := by
  have hxComp : x ∈ C := (mem_offCorridorComponentFinset C).1 hx
  obtain ⟨hxOff, _hxEq⟩ := ComponentCompl.mem_supp_iff.mp hxComp
  exact Finset.mem_sdiff.mpr
    ⟨Finset.mem_univ x, by simpa [supportFinset] using hxOff⟩

/-- A saturated three-vertex span-four component is an internal three-vertex
path between its extreme attachment vertices.  The three vertices occupy
the three strict interior BFS levels of the four-edge interval. -/
theorem IsGeodesic.triple_spanFour_geometry
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P)
    (C : OffCorridorComponent P) (l : ℕ)
    (hsize : (offCorridorComponentFinset C).card = 3)
    (hinterval : offCorridorComponentIntervalEdges P C =
      Finset.Ico l (l + 4)) :
    ∃ cL cM cR : V,
      offCorridorComponentFinset C = {cL, cM, cR} ∧
      cL ≠ cM ∧ cM ≠ cR ∧ cL ≠ cR ∧
      G.Adj cL cM ∧ G.Adj cM cR ∧
      G.Adj cL (P.getVert l) ∧
      G.Adj cR (P.getVert (l + 4)) ∧
      G.dist w cL = l + 1 ∧
      G.dist w cM = l + 2 ∧
      G.dist w cR = l + 3 := by
  classical
  obtain ⟨hleft, hright, _hbounds⟩ :=
    attachment_extrema_of_interval_eq_length P C l 4 (by omega) hinterval
  obtain ⟨hlLength, cL, hcL, hAdjL⟩ :=
    (mem_offCorridorAttachmentIndices P C l).1 hleft
  obtain ⟨hrLength, cR, hcR, hAdjR⟩ :=
    (mem_offCorridorAttachmentIndices P C (l + 4)).1 hright
  have hpathDist : G.dist (P.getVert l) (P.getVert (l + 4)) = 4 := by
    have h := hP.dist_getVert_eq_sub (i := l) (j := l + 4)
      (by omega) hrLength
    omega
  have hcLR : cL ≠ cR := by
    intro heq
    subst cR
    have hleftDist : G.dist (P.getVert l) cL = 1 :=
      dist_eq_one_iff_adj.mpr hAdjL.symm
    have hrightDist : G.dist cL (P.getVert (l + 4)) = 1 :=
      dist_eq_one_iff_adj.mpr hAdjR
    have htri := hconn.dist_triangle
      (u := P.getVert l) (v := cL) (w := P.getVert (l + 4))
    omega
  have hnotAdj : ¬ G.Adj cL cR := by
    intro hAdj
    have hleftDist : G.dist (P.getVert l) cL = 1 :=
      dist_eq_one_iff_adj.mpr hAdjL.symm
    have hmidDist : G.dist cL cR = 1 := dist_eq_one_iff_adj.mpr hAdj
    have hrightDist : G.dist cR (P.getVert (l + 4)) = 1 :=
      dist_eq_one_iff_adj.mpr hAdjR
    have htri₁ := hconn.dist_triangle
      (u := P.getVert l) (v := cL) (w := P.getVert (l + 4))
    have htri₂ := hconn.dist_triangle
      (u := cL) (v := cR) (w := P.getVert (l + 4))
    omega
  obtain ⟨W, hWPath, hWComp⟩ :=
    exists_isPath_support_subset_offCorridorComponent C hcL hcR
  have hsupportSubset : W.support.toFinset ⊆ offCorridorComponentFinset C := by
    intro z hz
    exact hWComp z (by simpa using hz)
  have hWCard : W.length + 1 ≤ 3 := by
    rw [← Walk.length_support,
      ← List.toFinset_card_of_nodup hWPath.support_nodup]
    simpa [hsize] using Finset.card_le_card hsupportSubset
  have hWPos : 1 ≤ W.length := by
    exact Nat.one_le_iff_ne_zero.mpr (fun hz =>
      hcLR (Walk.eq_of_length_eq_zero hz))
  have hWNeOne : W.length ≠ 1 := by
    intro hone
    exact hnotAdj (W.adj_of_length_eq_one hone)
  have hWLength : W.length = 2 := by omega
  let cM := W.getVert 1
  have hAdjLM : G.Adj cL cM := by
    simpa [cM] using W.adj_getVert_succ (i := 0) (by omega)
  have hAdjMR : G.Adj cM cR := by
    have h := W.adj_getVert_succ (i := 1) (by omega)
    have hend : W.getVert 2 = cR := by
      have := W.getVert_length
      rw [hWLength] at this
      exact this
    simpa [cM, hend] using h
  have hcLM : cL ≠ cM := hAdjLM.ne
  have hcMR : cM ≠ cR := hAdjMR.ne
  have hcM : cM ∈ offCorridorComponentFinset C := by
    apply hWComp
    exact W.getVert_mem_support 1
  have hcomponent : offCorridorComponentFinset C = {cL, cM, cR} := by
    have hsubset : ({cL, cM, cR} : Finset V) ⊆
        offCorridorComponentFinset C := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact hcL
      · exact hcM
      · exact hcR
    have htripleCard : ({cL, cM, cR} : Finset V).card = 3 := by
      simp [hcLM, hcLR, hcMR]
    symm
    apply Finset.eq_of_subset_of_card_le hsubset
    rw [hsize, htripleCard]
  have hleftLevel : G.dist w (P.getVert l) = l :=
    IsGeodesic.rootDist_getVert hP hlLength
  have hrightLevel : G.dist w (P.getVert (l + 4)) = l + 4 :=
    IsGeodesic.rootDist_getVert hP hrLength
  have hCLPath : G.dist cL cR ≤ 2 := by
    have := dist_le W
    omega
  have hlevelLUpper : G.dist w cL ≤ l + 1 := by
    have htri := hconn.dist_triangle
      (u := w) (v := P.getVert l) (w := cL)
    have hdist : G.dist (P.getVert l) cL = 1 :=
      dist_eq_one_iff_adj.mpr hAdjL.symm
    omega
  have hlevelLLower : l + 1 ≤ G.dist w cL := by
    have htri₁ := hconn.dist_triangle
      (u := w) (v := cL) (w := P.getVert (l + 4))
    have htri₂ := hconn.dist_triangle
      (u := cL) (v := cR) (w := P.getVert (l + 4))
    have hdistR : G.dist cR (P.getVert (l + 4)) = 1 :=
      dist_eq_one_iff_adj.mpr hAdjR
    omega
  have hlevelL : G.dist w cL = l + 1 := by omega
  have hlevelRLower : l + 3 ≤ G.dist w cR := by
    have htri := hconn.dist_triangle
      (u := w) (v := cR) (w := P.getVert (l + 4))
    have hdistR : G.dist cR (P.getVert (l + 4)) = 1 :=
      dist_eq_one_iff_adj.mpr hAdjR
    omega
  have hlevelRUpper : G.dist w cR ≤ l + 3 := by
    have htri₁ := hconn.dist_triangle (u := w) (v := cL) (w := cR)
    omega
  have hlevelR : G.dist w cR = l + 3 := by omega
  have hlevelMUpper : G.dist w cM ≤ l + 2 := by
    have htri := hconn.dist_triangle (u := w) (v := cL) (w := cM)
    have hdist : G.dist cL cM = 1 := dist_eq_one_iff_adj.mpr hAdjLM
    omega
  have hlevelMLower : l + 2 ≤ G.dist w cM := by
    have htri₁ := hconn.dist_triangle
      (u := w) (v := cM) (w := P.getVert (l + 4))
    have htri₂ := hconn.dist_triangle
      (u := cM) (v := cR) (w := P.getVert (l + 4))
    have hdistMR : G.dist cM cR = 1 := dist_eq_one_iff_adj.mpr hAdjMR
    have hdistR : G.dist cR (P.getVert (l + 4)) = 1 :=
      dist_eq_one_iff_adj.mpr hAdjR
    omega
  have hlevelM : G.dist w cM = l + 2 := by omega
  exact ⟨cL, cM, cR, hcomponent, hcLM, hcMR, hcLR,
    hAdjLM, hAdjMR, hAdjL, hAdjR, hlevelL, hlevelM, hlevelR⟩

/-- Rooted-level image form of `triple_spanFour_geometry`. -/
theorem IsGeodesic.image_rootDist_triple_spanFour
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P)
    (C : OffCorridorComponent P) (l : ℕ)
    (hsize : (offCorridorComponentFinset C).card = 3)
    (hinterval : offCorridorComponentIntervalEdges P C =
      Finset.Ico l (l + 4)) :
    (offCorridorComponentFinset C).image (G.dist w) =
      Finset.Ioo l (l + 4) := by
  obtain ⟨cL, cM, cR, hcomponent, _hcLM, _hcMR, _hcLR,
      _hAdjLM, _hAdjMR, _hAdjL, _hAdjR, hlevelL, hlevelM, hlevelR⟩ :=
    IsGeodesic.triple_spanFour_geometry hconn hP C l hsize hinterval
  ext k
  simp only [hcomponent, Finset.image_insert, Finset.image_singleton,
    Finset.mem_insert, Finset.mem_singleton, Finset.mem_Ioo]
  rw [hlevelL, hlevelM, hlevelR]
  omega

/-- In a disjoint tiling by intervals of length at least two, total excess
`sum (len-2)=2` is exactly the statement that the strict interiors contain
two adjacent-level starts.  This one lemma handles both pure-mass partitions
`4` and `3+3`. -/
theorem twoDefect_massIntervalProfile
    {α : Type*} [DecidableEq α]
    (components : Finset α) (lo len : α → ℕ) (s : ℕ)
    (hs : 2 ≤ s)
    (hunion : components.biUnion (blockInterval lo len) =
      Finset.range (2 * s - 2))
    (hdisjoint : (↑components : Set α).PairwiseDisjoint
      (blockInterval lo len))
    (hlen : ∀ c ∈ components, 2 ≤ len c)
    (hexcess : ∑ c ∈ components, (len c - 2) = 2) :
    let E := interiorLevels components lo len
    let H := (Finset.range (2 * s - 2)).filter fun r =>
      r ∈ E ∧ r + 1 ∈ E
    E.card = s ∧
      (∀ r < 2 * s - 2, r ∈ E ∨ r + 1 ∈ E) ∧
      H.card = 2 := by
  classical
  let interval := blockInterval lo len
  let interior := blockInterior lo len
  let E := interiorLevels components lo len
  let H := (Finset.range (2 * s - 2)).filter fun r =>
    r ∈ E ∧ r + 1 ∈ E
  let J : α → Finset ℕ := fun c =>
    Finset.Ioo (lo c) (lo c + len c - 1)
  have hcardInterval : ∀ c ∈ components, (interval c).card = len c := by
    intro c _
    simp [interval, blockInterval, Nat.card_Ico]
  have hsumLen : ∑ c ∈ components, len c = 2 * s - 2 := by
    have hcard := Finset.card_biUnion hdisjoint
    rw [hunion] at hcard
    simp only [Finset.card_range] at hcard
    rw [hcard]
    apply Finset.sum_congr rfl
    intro c hc
    exact (hcardInterval c hc).symm
  have hsumPred :
      (∑ c ∈ components, (len c - 2)) =
        (∑ c ∈ components, len c) - 2 * components.card := by
    rw [Finset.sum_tsub_distrib components hlen]
    simp only [Finset.sum_const, smul_eq_mul]
    omega
  have hcomponentsCard : components.card = s - 2 := by
    rw [hexcess, hsumLen] at hsumPred
    omega
  have hinteriorDisjoint :
      (↑components : Set α).PairwiseDisjoint interior :=
    pairwiseDisjoint_blockInterior components lo len hdisjoint
  have hcardInterior : ∀ c ∈ components,
      (interior c).card = len c - 1 := by
    intro c hc
    have hcLen := hlen c hc
    simp [interior, blockInterior, Nat.card_Ioo]
  have hsumInterior :
      ∑ c ∈ components, (len c - 1) =
        (∑ c ∈ components, len c) - components.card := by
    rw [Finset.sum_tsub_distrib components]
    · simp
    · intro c hc
      exact (hlen c hc).trans' (by omega)
  have hcardE : E.card = s := by
    have hcard := Finset.card_biUnion hinteriorDisjoint
    change (components.biUnion interior).card = s
    rw [hcard]
    calc
      (∑ c ∈ components, (interior c).card) =
          ∑ c ∈ components, (len c - 1) := by
        apply Finset.sum_congr rfl
        intro c hc
        exact hcardInterior c hc
      _ = (∑ c ∈ components, len c) - components.card := hsumInterior
      _ = s := by rw [hsumLen, hcomponentsCard]; omega
  have hcover : ∀ r < 2 * s - 2, r ∈ E ∨ r + 1 ∈ E := by
    intro r hr
    have hrUnion : r ∈ components.biUnion interval := by
      rw [show components.biUnion interval = Finset.range (2 * s - 2) by
        exact hunion]
      exact Finset.mem_range.mpr hr
    obtain ⟨c, hc, hrc⟩ := Finset.mem_biUnion.mp hrUnion
    have hbounds := Finset.mem_Ico.mp hrc
    by_cases hrl : lo c < r
    · left
      exact Finset.mem_biUnion.mpr
        ⟨c, hc, Finset.mem_Ioo.mpr ⟨hrl, hbounds.2⟩⟩
    · have hre : r = lo c := by omega
      right
      apply Finset.mem_biUnion.mpr
      refine ⟨c, hc, Finset.mem_Ioo.mpr ⟨by omega, ?_⟩⟩
      have hcLen := hlen c hc
      omega
  have hJsubset : ∀ c, J c ⊆ interval c := by
    intro c r hr
    have hrb := Finset.mem_Ioo.mp hr
    exact Finset.mem_Ico.mpr ⟨hrb.1.le, by omega⟩
  have hJdisjoint : (↑components : Set α).PairwiseDisjoint J := by
    intro a ha b hb hab
    exact (hdisjoint ha hb hab).mono (hJsubset a) (hJsubset b)
  have hHJ : H = components.biUnion J := by
    ext r
    constructor
    · intro hr
      have hrData := Finset.mem_filter.mp hr
      obtain ⟨c, hc, hrc⟩ := Finset.mem_biUnion.mp hrData.2.1
      obtain ⟨c', hc', hr1c'⟩ := Finset.mem_biUnion.mp hrData.2.2
      have hcc' : c = c' := by
        by_contra hne
        have hd := hdisjoint hc hc' hne
        have hrC : r ∈ interval c :=
          blockInterior_subset_blockInterval lo len c hrc
        have hrC' : r ∈ interval c' := by
          have hb := Finset.mem_Ioo.mp hr1c'
          exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
        exact (Finset.disjoint_left.mp hd hrC hrC').elim
      subst c'
      apply Finset.mem_biUnion.mpr
      refine ⟨c, hc, Finset.mem_Ioo.mpr ?_⟩
      have h0 := Finset.mem_Ioo.mp hrc
      have h1 := Finset.mem_Ioo.mp hr1c'
      omega
    · intro hr
      obtain ⟨c, hc, hrc⟩ := Finset.mem_biUnion.mp hr
      have hrb := Finset.mem_Ioo.mp hrc
      have hrInterval : r ∈ interval c := hJsubset c hrc
      have hrUnion : r ∈ components.biUnion interval :=
        Finset.mem_biUnion.mpr ⟨c, hc, hrInterval⟩
      have hrRange : r ∈ Finset.range (2 * s - 2) := by
        have hu : components.biUnion interval =
            Finset.range (2 * s - 2) := by simpa [interval] using hunion
        rw [hu] at hrUnion
        exact hrUnion
      apply Finset.mem_filter.mpr
      refine ⟨hrRange, ?_, ?_⟩
      · exact Finset.mem_biUnion.mpr
          ⟨c, hc, Finset.mem_Ioo.mpr ⟨hrb.1, by omega⟩⟩
      · exact Finset.mem_biUnion.mpr
          ⟨c, hc, Finset.mem_Ioo.mpr ⟨by omega, by omega⟩⟩
  have hcardJ : ∀ c ∈ components, (J c).card = len c - 2 := by
    intro c hc
    have hcLen := hlen c hc
    simp [J, Nat.card_Ioo]
    omega
  have hcardH : H.card = 2 := by
    rw [hHJ, Finset.card_biUnion hJdisjoint]
    calc
      (∑ c ∈ components, (J c).card) =
          ∑ c ∈ components, (len c - 2) := by
        apply Finset.sum_congr rfl
        intro c hc
        exact hcardJ c hc
      _ = 2 := hexcess
  exact ⟨hcardE, hcover, hcardH⟩

/-- Pure mass defect two gives a binary off-corridor BFS profile with exactly
two adjacent doubled-level gaps.  This simultaneously handles one
size-three component and two size-two components. -/
theorem IsGeodesic.pureMassTwoDefect_rootLevelProfile
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    [Fintype (OffCorridorComponent P)]
    (hconn : G.Connected) (color : G.Coloring Bool) (hP : IsGeodesic P)
    (hs : 2 ≤ slack P) (htwo : P.length = 2 * slack P - 2)
    (hnonbridge : ∀ i < P.length,
      ¬G.IsBridge s(P.getVert i, P.getVert (i + 1)))
    (hpure :
      let components := (Finset.univ : Finset (OffCorridorComponent P))
      let size : OffCorridorComponent P → ℕ := fun C =>
        (offCorridorComponentFinset C).card
      let span : OffCorridorComponent P → ℕ := fun C =>
        (offCorridorComponentIntervalEdges P C).card
      let unionCard :=
        (components.biUnion (offCorridorComponentIntervalEdges P)).card
      PureMassShape components size span (slack P) unionCard) :
    ∃ levels : Finset ℕ, ∃ high : Finset ℕ,
      levels.card = slack P ∧
      (∀ r < P.length, r ∈ levels ∨ r + 1 ∈ levels) ∧
      high = (Finset.range P.length).filter
        (fun r => r ∈ levels ∧ r + 1 ∈ levels) ∧
      high.card = 2 ∧
      levels ⊆ Finset.range P.length ∧
      (offCorridorFinset P).image (G.dist w) = levels ∧
      Set.InjOn (G.dist w) (offCorridorFinset P : Set V) := by
  classical
  let components : Finset (OffCorridorComponent P) := Finset.univ
  let size : OffCorridorComponent P → ℕ := fun C =>
    (offCorridorComponentFinset C).card
  let interval : OffCorridorComponent P → Finset ℕ :=
    offCorridorComponentIntervalEdges P
  let len : OffCorridorComponent P → ℕ := fun C => (interval C).card
  let unionCard := (components.biUnion interval).card
  change PureMassShape components size len (slack P) unionCard at hpure
  rcases hpure with ⟨hmassTwo, hspanZero, hoverlapZero, _hstructure⟩
  have hpositive : ∀ C ∈ components, 1 ≤ size C := by
    intro C _
    exact offCorridorComponentFinset_card_pos C
  have hmass : ∑ C ∈ components, size C = slack P := by
    have hraw := IsGeodesic.sum_offCorridorComponent_card_eq_slack hP
    convert hraw using 1
    refine Finset.sum_bij (fun C _ => C) ?_ ?_ ?_ ?_
    · intro C _
      simp [components]
    · intro C _ D _ hCD
      exact hCD
    · intro C _
      exact ⟨C, by simp [components], rfl⟩
    · intro C _
      rfl
  have hspan : ∀ C ∈ components, len C ≤ size C + 1 := by
    intro C _
    rw [show len C = offCorridorComponentSpan P C by
      simpa [len, interval] using card_offCorridorComponentIntervalEdges P C]
    exact hP.offCorridorComponentSpan_le_card_add_one C
  have hsaturated : ∀ C ∈ components, len C = size C + 1 := by
    apply all_span_saturated_of_spanDefect_eq_zero
      components size len hspan
    exact hspanZero
  have hsizeLe : ∀ C ∈ components, size C ≤ 3 := by
    intro C hC
    rcases _hstructure with hthree | hpair
    · obtain ⟨a, ha, haSize, _haSpan, hother⟩ := hthree
      by_cases hCa : C = a
      · subst C; omega
      · have := (hother C hC hCa).1
        omega
    · obtain ⟨a, ha, b, hb, hab, haSize, _haSpan,
          hbSize, _hbSpan, hother⟩ := hpair
      by_cases hCa : C = a
      · subst C; omega
      · by_cases hCb : C = b
        · subst C; omega
        · have := (hother C hC hCa hCb).1
          omega
  have hlenLower : ∀ C ∈ components, 2 ≤ len C := by
    intro C hC
    rw [hsaturated C hC]
    have := hpositive C hC
    omega
  have hexcess : ∑ C ∈ components, (len C - 2) = 2 := by
    have hpred : ∑ C ∈ components, (size C - 1) = 2 := by
      rw [← massDefect_eq_sum_pred components size (slack P)
        hpositive hmass]
      exact hmassTwo
    calc
      (∑ C ∈ components, (len C - 2)) =
          ∑ C ∈ components, (size C - 1) := by
        apply Finset.sum_congr rfl
        intro C hC
        rw [hsaturated C hC]
        omega
      _ = 2 := hpred
  have hintervalPos : ∀ C, 1 ≤ (interval C).card := by
    intro C
    change 1 ≤ len C
    have := hlenLower C (by simp [components])
    omega
  let hloExists : ∀ C : OffCorridorComponent P, ∃ l : ℕ,
      interval C = Finset.Ico l (l + len C) := fun C => by
    simpa [interval, len] using
      offCorridorInterval_eq_Ico_card P C (hintervalPos C)
  let lo : OffCorridorComponent P → ℕ := fun C =>
    Classical.choose (hloExists C)
  have hlo : ∀ C, interval C = blockInterval lo len C := by
    intro C
    simpa [blockInterval, lo] using Classical.choose_spec (hloExists C)
  have hunionActual : components.biUnion interval = Finset.range P.length := by
    have hraw :=
      IsGeodesic.biUnion_offCorridorIntervals_eq_range hP hnonbridge
    convert hraw using 1
    apply Finset.Subset.antisymm
    · intro i hi
      obtain ⟨C, _hC, hiC⟩ := Finset.mem_biUnion.mp hi
      exact Finset.mem_biUnion.mpr ⟨C, by simp, hiC⟩
    · intro i hi
      obtain ⟨C, _hC, hiC⟩ := Finset.mem_biUnion.mp hi
      exact Finset.mem_biUnion.mpr ⟨C, by simp [components], hiC⟩
  have hunion : components.biUnion (blockInterval lo len) =
      Finset.range (2 * slack P - 2) := by
    have hfamily : blockInterval lo len = interval := by
      funext C
      exact (hlo C).symm
    rw [← htwo, hfamily]
    exact hunionActual
  have hdisjointActual :
      (components : Set (OffCorridorComponent P)).PairwiseDisjoint interval := by
    apply pairwiseDisjoint_of_overlapDefect_eq_zero components interval
    exact hoverlapZero
  have hdisjoint :
      (components : Set (OffCorridorComponent P)).PairwiseDisjoint
        (blockInterval lo len) := by
    have hfamily : blockInterval lo len = interval := by
      funext C
      exact (hlo C).symm
    rw [hfamily]
    exact hdisjointActual
  let levels := interiorLevels components lo len
  let high := (Finset.range P.length).filter fun r =>
    r ∈ levels ∧ r + 1 ∈ levels
  obtain ⟨hlevelsCard, hactiveRaw, hhighRaw⟩ :=
    twoDefect_massIntervalProfile components lo len (slack P)
      hs hunion hdisjoint hlenLower hexcess
  have hactive : ∀ r < P.length,
      r ∈ levels ∨ r + 1 ∈ levels := by
    simpa [htwo, levels] using hactiveRaw
  have hhighCard : high.card = 2 := by
    simpa [high, levels, htwo] using hhighRaw
  have hlevelsSub : levels ⊆ Finset.range P.length := by
    intro k hk
    obtain ⟨C, hC, hkC⟩ := Finset.mem_biUnion.mp hk
    have hkInterval : k ∈ blockInterval lo len C :=
      blockInterior_subset_blockInterval lo len C hkC
    have hkActual : k ∈ interval C := by simpa [hlo C] using hkInterval
    have hkUnion : k ∈ components.biUnion interval :=
      Finset.mem_biUnion.mpr ⟨C, hC, hkActual⟩
    rw [hunionActual] at hkUnion
    exact hkUnion
  have himageComponent : ∀ C,
      (offCorridorComponentFinset C).image (G.dist w) =
        blockInterior lo len C := by
    intro C
    have hC : C ∈ components := by simp [components]
    have hpos := hpositive C hC
    have hle := hsizeLe C hC
    have hsat := hsaturated C hC
    have hinterval := hlo C
    have hcases : size C = 1 ∨ size C = 2 ∨ size C = 3 := by omega
    rcases hcases with hunit | hpairSize | htriple
    · have hlenC : len C = 2 := by omega
      have hspanTwo : interval C = Finset.Ico (lo C) (lo C + 2) := by
        simpa [blockInterval, hlenC] using hinterval
      simpa [size, interval, blockInterior, hlenC] using
        IsGeodesic.image_rootDist_singleton_spanTwo
          hconn hP C (lo C) hunit hspanTwo
    · have hlenC : len C = 3 := by omega
      have hspanThree : interval C = Finset.Ico (lo C) (lo C + 3) := by
        simpa [blockInterval, hlenC] using hinterval
      simpa [size, interval, blockInterior, hlenC] using
        IsGeodesic.image_rootDist_pair_spanThree
          hconn color hP C (lo C) hpairSize hspanThree
    · have hlenC : len C = 4 := by omega
      have hspanFour : interval C = Finset.Ico (lo C) (lo C + 4) := by
        simpa [blockInterval, hlenC] using hinterval
      simpa [size, interval, blockInterior, hlenC] using
        IsGeodesic.image_rootDist_triple_spanFour
          hconn hP C (lo C) htriple hspanFour
  have himage : (offCorridorFinset P).image (G.dist w) = levels := by
    ext k
    constructor
    · intro hk
      obtain ⟨x, hxoff, rfl⟩ := Finset.mem_image.mp hk
      have hxnot : x ∉ P.support := by
        have hxsupp : x ∉ supportFinset P := (Finset.mem_sdiff.mp hxoff).2
        simpa [supportFinset] using hxsupp
      let C := offCorridorComponentOf P x hxnot
      have hxC : x ∈ offCorridorComponentFinset C :=
        mem_offCorridorComponentOf P hxnot
      have hlevelC : G.dist w x ∈ blockInterior lo len C := by
        rw [← himageComponent C]
        exact Finset.mem_image.mpr ⟨x, hxC, rfl⟩
      exact Finset.mem_biUnion.mpr
        ⟨C, by simp [components], hlevelC⟩
    · intro hk
      obtain ⟨C, _hC, hkC⟩ := Finset.mem_biUnion.mp hk
      rw [← himageComponent C] at hkC
      obtain ⟨x, hxC, hxlevel⟩ := Finset.mem_image.mp hkC
      have hxComp : x ∈ C := (mem_offCorridorComponentFinset C).1 hxC
      obtain ⟨hxnot, _⟩ := ComponentCompl.mem_supp_iff.mp hxComp
      apply Finset.mem_image.mpr
      refine ⟨x, ?_, hxlevel⟩
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ x, by simpa [supportFinset] using hxnot⟩
  have hoffCard : (offCorridorFinset P).card = slack P := by
    rw [show offCorridorFinset P =
        (Finset.univ : Finset V) \ supportFinset P by rfl,
      Finset.card_sdiff]
    simp only [Finset.inter_univ, Finset.card_univ, slack]
    have hsupp := hP.card_supportFinset
    have hle : P.length + 1 ≤ Fintype.card V := by
      rw [← hsupp]
      exact Finset.card_le_univ _
    omega
  have hinjective : Set.InjOn (G.dist w) (offCorridorFinset P : Set V) := by
    apply Finset.card_image_iff.mp
    rw [himage, hlevelsCard, hoffCard]
  exact ⟨levels, high, hlevelsCard, hactive,
    rfl, hhighCard, hlevelsSub, himage, hinjective⟩

/-- Graph-level threshold-cut wrapper for the saturated size-three
one-exception matrix theorem.  The structural input is now only literal
level alignment away from one row, its exact local `(D,L)` data, and the
two-high residual cut profile. -/
theorem totalCost_le_rlBudget_of_q3_twoHighLevelCuts
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (w x₀ : V) (m₁ m₂ : I → V) (level : V → ℕ)
    (s d : ℕ) (capacity : Fin d → ℕ) (high : Finset (Fin d))
    (exceptional : I)
    (hs : 5 ≤ s) (hd : d = 2 * s - 2)
    (hroot : level w = 0) (hstub : level x₀ = d)
    (hendpoint₁ : ∀ i, level (m₁ i) ≤ d)
    (hendpoint₂ : ∀ i, level (m₂ i) ≤ d)
    (haligned : ∀ i, i ≠ exceptional →
      G.dist (m₁ i) (m₂ i) =
        Nat.dist (level (m₁ i)) (level (m₂ i)))
    (hq3 : G.dist (m₁ exceptional) (m₂ exceptional) = 4 ∧
      (Nat.dist (level (m₁ exceptional)) (level (m₂ exceptional)) = 0 ∨
        Nat.dist (level (m₁ exceptional)) (level (m₂ exceptional)) = 2))
    (hRFC : ∀ T : Finset V, w ∉ T →
      (∑ i : I, separationDemand T (m₁ i) (m₂ i)) +
        (if x₀ ∈ T then 1 else 0) ≤ cutSize G T)
    (hcut : ∀ r : Fin d,
      cutSize G (levelUpperCut level r.1) ≤ capacity r + 1)
    (hlegal : ∀ i, 4 ≤ G.dist (m₁ i) (m₂ i))
    (hhigh : high.card ≤ 2)
    (hcapacity : ∀ r, capacity r ≤ if r ∈ high then 3 else 1) :
    (∑ i : I, (G.dist (m₁ i) (m₂ i) + 1) ^ 2) ≤
      rlBudget s d := by
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
  have hthreshold : ∀ i,
      (∑ r : Fin d, cross i r) =
        Nat.dist (level (m₁ i)) (level (m₂ i)) := by
    intro i
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
    exact sum_thresholdSeparation_eq_dist
      (hendpoint₁ i) (hendpoint₂ i)
  have hmatrixAligned : ∀ i, i ≠ exceptional →
      G.dist (m₁ i) (m₂ i) = ∑ r : Fin d, cross i r := by
    intro i hie
    rw [haligned i hie, hthreshold i]
  have hmatrixQ3 : G.dist (m₁ exceptional) (m₂ exceptional) = 4 ∧
      ((∑ r : Fin d, cross exceptional r) = 0 ∨
        (∑ r : Fin d, cross exceptional r) = 2) := by
    rw [hthreshold exceptional]
    exact hq3
  have hcolumn : ∀ r : Fin d,
      (∑ i : I, cross i r) ≤ capacity r := by
    intro r
    have hw : w ∉ levelUpperCut level r.1 := by simp [hroot]
    have hx : x₀ ∈ levelUpperCut level r.1 := by simp [hstub, r.2]
    have hvalid := hRFC (levelUpperCut level r.1) hw
    simp only [hx, if_true] at hvalid
    exact Nat.le_of_add_le_add_right (hvalid.trans (hcut r))
  exact totalCost_le_rlBudget_of_q3_twoHighColumns
    (fun i => G.dist (m₁ i) (m₂ i)) d s cross capacity high exceptional
    hs hd hcross hmatrixAligned hmatrixQ3 hcolumn hlegal hhigh hcapacity

/-- A q3 level-cut profile with zero or one exceptional row.  The zero-row
case uses weights `2` on the two high columns and `1` elsewhere; the one-row
case invokes the exact q3 surcharge theorem. -/
theorem totalCost_le_rlBudget_of_q3_zeroOrOneExceptionLevelCuts
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (w x₀ : V) (m₁ m₂ : I → V) (level : V → ℕ)
    (s d : ℕ) (capacity : Fin d → ℕ) (high : Finset (Fin d))
    (hs : 5 ≤ s) (hd : d = 2 * s - 2)
    (hroot : level w = 0) (hstub : level x₀ = d)
    (hendpoint₁ : ∀ i, level (m₁ i) ≤ d)
    (hendpoint₂ : ∀ i, level (m₂ i) ≤ d)
    (hclass : ∀ i,
      G.dist (m₁ i) (m₂ i) =
          Nat.dist (level (m₁ i)) (level (m₂ i)) ∨
        (G.dist (m₁ i) (m₂ i) = 4 ∧
          (Nat.dist (level (m₁ i)) (level (m₂ i)) = 0 ∨
            Nat.dist (level (m₁ i)) (level (m₂ i)) = 2)))
    (hexceptionCount :
      ((Finset.univ : Finset I).filter fun i =>
        G.dist (m₁ i) (m₂ i) ≠
          Nat.dist (level (m₁ i)) (level (m₂ i))).card ≤ 1)
    (hRFC : ∀ T : Finset V, w ∉ T →
      (∑ i : I, separationDemand T (m₁ i) (m₂ i)) +
        (if x₀ ∈ T then 1 else 0) ≤ cutSize G T)
    (hcut : ∀ r : Fin d,
      cutSize G (levelUpperCut level r.1) ≤ capacity r + 1)
    (hlegal : ∀ i, 4 ≤ G.dist (m₁ i) (m₂ i))
    (hhigh : high.card ≤ 2)
    (hcapacity : ∀ r, capacity r ≤ if r ∈ high then 3 else 1) :
    (∑ i : I, (G.dist (m₁ i) (m₂ i) + 1) ^ 2) ≤
      rlBudget s d := by
  classical
  let exceptional : Finset I :=
    (Finset.univ : Finset I).filter fun i =>
      G.dist (m₁ i) (m₂ i) ≠
        Nat.dist (level (m₁ i)) (level (m₂ i))
  by_cases hempty : exceptional = ∅
  · have haligned : ∀ i,
        G.dist (m₁ i) (m₂ i) =
          Nat.dist (level (m₁ i)) (level (m₂ i)) := by
      intro i
      by_contra hi
      have : i ∈ exceptional := by simp [exceptional, hi]
      rw [hempty] at this
      simp at this
    let indicator : Fin d → ℕ := fun r => if r ∈ high then 1 else 0
    let weight : Fin d → ℕ := fun r => 1 + indicator r
    have hindicatorSum : (∑ r : Fin d, indicator r) = high.card := by
      simp [indicator]
    have hweight : (∑ r : Fin d, weight r) ≤ 2 * s := by
      have heq : (∑ r : Fin d, weight r) = d + high.card := by
        simp only [weight, Finset.sum_add_distrib]
        rw [hindicatorSum]
        simp
      calc
        (∑ r : Fin d, weight r) = d + high.card := heq
        _ ≤ 2 * s := by omega
    have hcapacityWeight : ∀ r, capacity r ≤ (weight r) ^ 2 := by
      intro r
      by_cases hr : r ∈ high
      · have hrCap := hcapacity r
        simp [weight, indicator, hr] at hrCap ⊢
        omega
      · simpa [weight, indicator, hr] using hcapacity r
    have hprofile := twoHighColumns_fin_profile_bounds d capacity high
      hhigh hcapacity
    have hcapacitySum : (∑ r : Fin d, capacity r) ≤ 2 * s + 2 := by
      exact hprofile.1.trans (by omega)
    exact totalCost_le_rlBudget_of_nearBoundaryCapacityProfile
      w x₀ m₁ m₂ level s d capacity weight
      (by omega) (Or.inr hd) hcapacityWeight hweight hcapacitySum
      hroot hstub hendpoint₁ hendpoint₂ haligned hRFC hcut hlegal
  · have hnonempty : exceptional.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨e, he⟩ := hnonempty
    have heExceptional :
        G.dist (m₁ e) (m₂ e) ≠
          Nat.dist (level (m₁ e)) (level (m₂ e)) :=
      (Finset.mem_filter.mp he).2
    have hcard : exceptional.card ≤ 1 := by
      simpa [exceptional] using hexceptionCount
    have haligned : ∀ i, i ≠ e →
        G.dist (m₁ i) (m₂ i) =
          Nat.dist (level (m₁ i)) (level (m₂ i)) := by
      intro i hie
      by_contra hi
      have hiMem : i ∈ exceptional := by simp [exceptional, hi]
      have hij : i = e :=
        (Finset.card_le_one.mp hcard) i hiMem e he
      exact hie hij
    have heClass := hclass e
    have heQ3 : G.dist (m₁ e) (m₂ e) = 4 ∧
        (Nat.dist (level (m₁ e)) (level (m₂ e)) = 0 ∨
          Nat.dist (level (m₁ e)) (level (m₂ e)) = 2) := by
      rcases heClass with heAligned | heQ3
      · exact (heExceptional heAligned).elim
      · exact heQ3
    exact totalCost_le_rlBudget_of_q3_twoHighLevelCuts
      w x₀ m₁ m₂ level s d capacity high e hs hd hroot hstub
      hendpoint₁ hendpoint₂ haligned heQ3 hRFC hcut hlegal hhigh hcapacity

/-- Reusable aligned landing for a binary rooted-level profile with at most
two adjacent doubled-level gaps. -/
theorem totalCost_le_rlBudget_of_aligned_twoHighRootLevelProfile
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀} (m₁ m₂ : I → V)
    (levels high : Finset ℕ) (s d : ℕ)
    (hs : 5 ≤ s) (hd : P.length = d) (hrow : d = 2 * s - 2)
    (hP : IsGeodesic P)
    (hactive : ∀ r < d, r ∈ levels ∨ r + 1 ∈ levels)
    (hhighEq : high = (Finset.range d).filter
      (fun r => r ∈ levels ∧ r + 1 ∈ levels))
    (hhighCard : high.card ≤ 2)
    (hlevelsSub : levels ⊆ Finset.range d)
    (himage : (offCorridorFinset P).image (G.dist w) = levels)
    (hinjective : Set.InjOn (G.dist w) (offCorridorFinset P : Set V))
    (hvertexBound : ∀ v : V, G.dist w v ≤ d)
    (hstep : ∀ {u v : V}, G.Adj u v →
      Nat.dist (G.dist w u) (G.dist w v) = 1)
    (haligned : ∀ i,
      G.dist (m₁ i) (m₂ i) =
        Nat.dist (G.dist w (m₁ i)) (G.dist w (m₂ i)))
    (hRFC : ∀ T : Finset V, w ∉ T →
      (∑ i : I, separationDemand T (m₁ i) (m₂ i)) +
        (if x₀ ∈ T then 1 else 0) ≤ cutSize G T)
    (hlegal : ∀ i, 4 ≤ G.dist (m₁ i) (m₂ i)) :
    (∑ i : I, (G.dist (m₁ i) (m₂ i) + 1) ^ 2) ≤ rlBudget s d := by
  classical
  let extra : ℕ → ℕ := fun k => if k ∈ levels then 1 else 0
  let capacity : Fin d → ℕ := fun r =>
    extra r.1 + extra (r.1 + 1) + extra r.1 * extra (r.1 + 1)
  let highFin : Finset (Fin d) :=
    (Finset.univ : Finset (Fin d)).filter fun r => r.1 ∈ high
  have hhighSub : high ⊆ Finset.range d := by
    intro k hk
    rw [hhighEq] at hk
    exact (Finset.mem_filter.mp hk).1
  have himageHigh : highFin.image Fin.val = high := by
    ext k
    constructor
    · intro hk
      obtain ⟨r, hr, hrk⟩ := Finset.mem_image.mp hk
      have hrHigh : r.1 ∈ high := by simpa [highFin] using hr
      simpa [← hrk] using hrHigh
    · intro hk
      let r : Fin d := ⟨k, Finset.mem_range.mp (hhighSub hk)⟩
      exact Finset.mem_image.mpr ⟨r, by simp [highFin, r, hk], rfl⟩
  have hhighFinCard : highFin.card ≤ 2 := by
    have hinj : Set.InjOn Fin.val (highFin : Set (Fin d)) :=
      fun _ _ _ _ h => Fin.ext h
    have hcardEq : (highFin.image Fin.val).card = highFin.card :=
      Finset.card_image_iff.mpr hinj
    rw [himageHigh] at hcardEq
    omega
  have hlayer : ∀ k ≤ d,
      (levelLayer (G.dist w) k).card = extra k + 1 := by
    intro k hk
    have h := IsGeodesic.levelLayer_card_eq_one_add_indicator
      hP levels hinjective himage (k := k) (by omega)
    simpa [extra, Nat.add_comm] using h
  have hcut : ∀ r : Fin d,
      cutSize G (levelUpperCut (G.dist w) r.1) ≤ capacity r + 1 := by
    intro r
    have hproduct := cutSize_levelUpperCut_le_layerProduct
      (G.dist w) hstep r.1
    rw [hlayer r.1 (by omega), hlayer (r.1 + 1) (by omega)] at hproduct
    dsimp [capacity]
    nlinarith
  have hcapacity : ∀ r, capacity r ≤ if r ∈ highFin then 3 else 1 := by
    intro r
    have hact := hactive r.1 r.2
    by_cases h0 : r.1 ∈ levels
    · by_cases h1 : r.1 + 1 ∈ levels
      · have hrHigh : r ∈ highFin := by
          simp [highFin, hhighEq, h0, h1]
        simp [capacity, extra, h0, h1, hrHigh]
      · have hrNot : r ∉ highFin := by
          simp [highFin, hhighEq, h1]
        simp [capacity, extra, h0, h1, hrNot]
    · by_cases h1 : r.1 + 1 ∈ levels
      · have hrNot : r ∉ highFin := by
          simp [highFin, hhighEq, h0]
        simp [capacity, extra, h0, h1, hrNot]
      · exfalso
        exact hact.elim h0 h1
  have hroot : G.dist w w = 0 := by simp
  have hstub : G.dist w x₀ = d := by simpa [← hd] using hP.symm
  have hzero :
      ((Finset.univ : Finset I).filter fun i =>
        G.dist (m₁ i) (m₂ i) ≠
          Nat.dist (G.dist w (m₁ i)) (G.dist w (m₂ i))).card ≤ 1 := by
    simp [haligned]
  exact totalCost_le_rlBudget_of_q3_zeroOrOneExceptionLevelCuts
    w x₀ m₁ m₂ (G.dist w) s d capacity highFin hs hrow hroot hstub
    (fun i => hvertexBound (m₁ i)) (fun i => hvertexBound (m₂ i))
    (fun i => Or.inl (haligned i)) hzero hRFC hcut hlegal
    hhighFinCard hcapacity

/-- Away from the three vertices of the saturated size-three block, every
vertex in the pure-mass `q3` geometry has the two corridor anchors dictated
by its BFS level. -/
theorem IsGeodesic.q3PureMass_regular_twoSidedAnchors
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ v cL cM cR : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P)
    (Cstar : OffCorridorComponent P)
    (hstar : offCorridorComponentFinset Cstar = {cL, cM, cR})
    (hothers : ∀ C : OffCorridorComponent P, C ≠ Cstar →
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2)
    (hvL : v ≠ cL) (hvM : v ≠ cM) (hvR : v ≠ cR) :
    (G.dist w v < P.length →
      G.Adj v (P.getVert (G.dist w v + 1))) ∧
    (0 < G.dist w v →
      G.Adj (P.getVert (G.dist w v - 1)) v) := by
  classical
  by_cases hvSupport : v ∈ P.support
  · have hvEq := IsGeodesic.eq_getVert_of_mem_support_rootDist_eq
      hP hvSupport (k := G.dist w v) rfl
    let j := P.support.idxOf v
    have hj : j ≤ P.length := support_idxOf_le_length P hvSupport
    have hget : P.getVert j = v := P.getVert_support_idxOf hvSupport
    have hlevelJ := IsGeodesic.rootDist_getVert hP hj
    have hvBound : G.dist w v ≤ P.length := by
      rw [hget] at hlevelJ
      omega
    constructor
    · intro hvlt
      have hadj := P.adj_getVert_succ (i := G.dist w v) hvlt
      rw [← hvEq] at hadj
      exact hadj
    · intro hvpos
      have hadj := P.adj_getVert_succ (i := G.dist w v - 1) (by omega)
      have hsucc : G.dist w v - 1 + 1 = G.dist w v := by omega
      rw [hsucc, ← hvEq] at hadj
      exact hadj
  · have hvNot : v ∉ P.support := hvSupport
    let C := offCorridorComponentOf P v hvNot
    have hvC : v ∈ offCorridorComponentFinset C :=
      mem_offCorridorComponentOf P hvNot
    have hCne : C ≠ Cstar := by
      intro hEq
      have hvStar : v ∈ offCorridorComponentFinset Cstar := by
        simpa [hEq] using hvC
      have hvCases : v = cL ∨ v = cM ∨ v = cR := by
        simpa [hstar] using hvStar
      rcases hvCases with h | h | h
      · exact hvL h
      · exact hvM h
      · exact hvR h
    obtain ⟨hsize, hspan⟩ := hothers C hCne
    obtain ⟨l, hinterval⟩ :=
      offCorridorInterval_eq_Ico_of_card_eq_two P C hspan
    obtain ⟨c, hset, hlevel, hleft, hright⟩ :=
      IsGeodesic.singleton_spanTwo_geometry hconn hP C l hsize hinterval
    have hvc : v = c := by simpa [hset] using hvC
    subst v
    constructor
    · intro _
      simpa [hlevel] using hright
    · intro _
      simpa [hlevel] using hleft.symm

/-- Away from the four vertices of two saturated size-two blocks, every
vertex has its two canonical corridor anchors. -/
theorem IsGeodesic.q2q2PureMass_regular_twoSidedAnchors
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ v aL aR bL bR : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P)
    (Ca Cb : OffCorridorComponent P)
    (hCa : offCorridorComponentFinset Ca = {aL, aR})
    (hCb : offCorridorComponentFinset Cb = {bL, bR})
    (hothers : ∀ C : OffCorridorComponent P, C ≠ Ca → C ≠ Cb →
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2)
    (hvaL : v ≠ aL) (hvaR : v ≠ aR)
    (hvbL : v ≠ bL) (hvbR : v ≠ bR) :
    (G.dist w v < P.length →
      G.Adj v (P.getVert (G.dist w v + 1))) ∧
    (0 < G.dist w v →
      G.Adj (P.getVert (G.dist w v - 1)) v) := by
  classical
  by_cases hvSupport : v ∈ P.support
  · have hvEq := IsGeodesic.eq_getVert_of_mem_support_rootDist_eq
      hP hvSupport (k := G.dist w v) rfl
    have hvBound : G.dist w v ≤ P.length := by
      let j := P.support.idxOf v
      have hj : j ≤ P.length := support_idxOf_le_length P hvSupport
      have hget : P.getVert j = v := P.getVert_support_idxOf hvSupport
      have hlevel := IsGeodesic.rootDist_getVert hP hj
      rw [hget] at hlevel
      omega
    constructor
    · intro hvlt
      have hadj := P.adj_getVert_succ (i := G.dist w v) hvlt
      rw [← hvEq] at hadj
      exact hadj
    · intro hvpos
      have hadj := P.adj_getVert_succ (i := G.dist w v - 1) (by omega)
      have hsucc : G.dist w v - 1 + 1 = G.dist w v := by omega
      rw [hsucc, ← hvEq] at hadj
      exact hadj
  · let C := offCorridorComponentOf P v hvSupport
    have hvC : v ∈ offCorridorComponentFinset C :=
      mem_offCorridorComponentOf P hvSupport
    have hCneA : C ≠ Ca := by
      intro hEq
      have hvA : v ∈ offCorridorComponentFinset Ca := by simpa [hEq] using hvC
      have hvCases : v = aL ∨ v = aR := by simpa [hCa] using hvA
      exact hvCases.elim hvaL hvaR
    have hCneB : C ≠ Cb := by
      intro hEq
      have hvB : v ∈ offCorridorComponentFinset Cb := by simpa [hEq] using hvC
      have hvCases : v = bL ∨ v = bR := by simpa [hCb] using hvB
      exact hvCases.elim hvbL hvbR
    obtain ⟨hsize, hspan⟩ := hothers C hCneA hCneB
    obtain ⟨l, hinterval⟩ :=
      offCorridorInterval_eq_Ico_of_card_eq_two P C hspan
    obtain ⟨c, hset, hlevel, hleft, hright⟩ :=
      IsGeodesic.singleton_spanTwo_geometry hconn hP C l hsize hinterval
    have hvc : v = c := by simpa [hset] using hvC
    subst v
    constructor
    · intro _
      simpa [hlevel] using hright
    · intro _
      simpa [hlevel] using hleft.symm

/-- Route from a special vertex to a regular vertex on its right through a
corridor endpoint, with no loss over the BFS-level difference. -/
theorem IsGeodesic.dist_le_levelSub_of_rightEndpointRoute
    {V : Type*} {G : SimpleGraph V} {w x₀ z y : V}
    {P : G.Walk w x₀} (hconn : G.Connected) (hP : IsGeodesic P)
    {a e b : ℕ} (hae : a ≤ e) (heb : e + 1 ≤ b)
    (hb : b ≤ P.length)
    (hz : G.dist z (P.getVert e) ≤ e - a)
    (hy : G.Adj (P.getVert (b - 1)) y) :
    G.dist z y ≤ b - a := by
  have heLast : e ≤ b - 1 := by omega
  have hbLast : b - 1 ≤ P.length := by omega
  have hpath := hP.dist_getVert_eq_sub heLast hbLast
  have hyDist : G.dist (P.getVert (b - 1)) y = 1 :=
    dist_eq_one_iff_adj.mpr hy
  have htri₁ := hconn.dist_triangle (u := z) (v := P.getVert e) (w := y)
  have htri₂ := hconn.dist_triangle
    (u := P.getVert e) (v := P.getVert (b - 1)) (w := y)
  omega

/-- Left-right symmetric endpoint route. -/
theorem IsGeodesic.dist_le_levelSub_of_leftEndpointRoute
    {V : Type*} {G : SimpleGraph V} {w x₀ x z : V}
    {P : G.Walk w x₀} (hconn : G.Connected) (hP : IsGeodesic P)
    {a e b : ℕ} (hae : a + 1 ≤ e) (heb : e ≤ b)
    (hb : b ≤ P.length)
    (hx : G.Adj x (P.getVert (a + 1)))
    (hz : G.dist (P.getVert e) z ≤ b - e) :
    G.dist x z ≤ b - a := by
  have haNext : a + 1 ≤ P.length := by omega
  have hpath := hP.dist_getVert_eq_sub hae (heb.trans hb)
  have hxDist : G.dist x (P.getVert (a + 1)) = 1 :=
    dist_eq_one_iff_adj.mpr hx
  have htri₁ := hconn.dist_triangle (u := x) (v := P.getVert (a + 1)) (w := z)
  have htri₂ := hconn.dist_triangle
    (u := P.getVert (a + 1)) (v := P.getVert e) (w := z)
  omega

/-- Route between two vertices through a corridor segment when both
vertices have bounded access to (possibly different) corridor endpoints. -/
theorem IsGeodesic.dist_le_levelSub_of_twoEndpointRoutes
    {V : Type*} {G : SimpleGraph V} {w x₀ x y : V}
    {P : G.Walk w x₀} (hconn : G.Connected) (hP : IsGeodesic P)
    {a e f b : ℕ} (hae : a ≤ e) (hef : e ≤ f) (hfb : f ≤ b)
    (hf : f ≤ P.length)
    (hx : G.dist x (P.getVert e) ≤ e - a)
    (hy : G.dist (P.getVert f) y ≤ b - f) :
    G.dist x y ≤ b - a := by
  have hpath := hP.dist_getVert_eq_sub hef hf
  have htri₁ := hconn.dist_triangle
    (u := x) (v := P.getVert e) (w := y)
  have htri₂ := hconn.dist_triangle
    (u := P.getVert e) (v := P.getVert f) (w := y)
  omega

/-- At a BFS level occupied by one named off-corridor vertex, every graph
vertex on that level is either the corridor vertex or that named vertex. -/
theorem IsGeodesic.eq_getVert_or_eq_offVertex_of_level
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ c v : V} {P : G.Walk w x₀}
    (hP : IsGeodesic P)
    (hinjective : Set.InjOn (G.dist w) (offCorridorFinset P : Set V))
    (hc : c ∈ offCorridorFinset P) {k : ℕ}
    (hck : G.dist w c = k) (hvk : G.dist w v = k) :
    v = P.getVert k ∨ v = c := by
  by_cases hvSupport : v ∈ P.support
  · left
    exact IsGeodesic.eq_getVert_of_mem_support_rootDist_eq
      hP hvSupport hvk
  · right
    have hvOff : v ∈ offCorridorFinset P :=
      Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ v, by simpa [supportFinset] using hvSupport⟩
    exact hinjective hvOff hc (by omega)

theorem IsGeodesic.dist_namedOffVertex_sameLevel_le_two
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ c v : V} {P : G.Walk w x₀}
    (hP : IsGeodesic P)
    (hinjective : Set.InjOn (G.dist w) (offCorridorFinset P : Set V))
    (hc : c ∈ offCorridorFinset P) {k : ℕ}
    (hck : G.dist w c = k) (hvk : G.dist w v = k)
    (hclose : G.dist c (P.getVert k) ≤ 2) :
    G.dist c v ≤ 2 := by
  rcases IsGeodesic.eq_getVert_or_eq_offVertex_of_level
    hP hinjective hc hck hvk with hv | hv
  · simpa [hv] using hclose
  · subst v
    simp

/-- Two regular vertices on one pure-mass BFS level are at distance at most
two, so they can never form a legal internal demand. -/
theorem IsGeodesic.q3PureMass_regular_sameLevel_dist_le_two
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ x y cL cM cR : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P)
    (Cstar : OffCorridorComponent P)
    (hstar : offCorridorComponentFinset Cstar = {cL, cM, cR})
    (hothers : ∀ C : OffCorridorComponent P, C ≠ Cstar →
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2)
    (hxL : x ≠ cL) (hxM : x ≠ cM) (hxR : x ≠ cR)
    (hyL : y ≠ cL) (hyM : y ≠ cM) (hyR : y ≠ cR)
    (hlevel : G.dist w x = G.dist w y) :
    G.dist x y ≤ 2 := by
  by_cases hzero : G.dist w x = 0
  · have hxw : x = w :=
      ((hconn.dist_eq_zero_iff (u := w) (v := x)).mp hzero).symm
    have hyzero : G.dist w y = 0 := by omega
    have hyw : y = w :=
      ((hconn.dist_eq_zero_iff (u := w) (v := y)).mp hyzero).symm
    subst x
    subst y
    simp
  · have hxAnchor :=
      (IsGeodesic.q3PureMass_regular_twoSidedAnchors
        hconn hP Cstar hstar hothers hxL hxM hxR).2 (by omega)
    have hyAnchor :=
      (IsGeodesic.q3PureMass_regular_twoSidedAnchors
        hconn hP Cstar hstar hothers hyL hyM hyR).2 (by omega)
    have hsameAnchor : G.dist w x - 1 = G.dist w y - 1 := by omega
    rw [hsameAnchor] at hxAnchor
    have hxDist : G.dist x (P.getVert (G.dist w y - 1)) = 1 :=
      dist_eq_one_iff_adj.mpr hxAnchor.symm
    have hyDist : G.dist (P.getVert (G.dist w y - 1)) y = 1 :=
      dist_eq_one_iff_adj.mpr hyAnchor
    have htri := hconn.dist_triangle
      (u := x) (v := P.getVert (G.dist w y - 1)) (w := y)
    omega

theorem IsGeodesic.q2q2PureMass_regular_sameLevel_dist_le_two
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ x y aL aR bL bR : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P)
    (Ca Cb : OffCorridorComponent P)
    (hCa : offCorridorComponentFinset Ca = {aL, aR})
    (hCb : offCorridorComponentFinset Cb = {bL, bR})
    (hothers : ∀ C : OffCorridorComponent P, C ≠ Ca → C ≠ Cb →
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2)
    (hxaL : x ≠ aL) (hxaR : x ≠ aR)
    (hxbL : x ≠ bL) (hxbR : x ≠ bR)
    (hyaL : y ≠ aL) (hyaR : y ≠ aR)
    (hybL : y ≠ bL) (hybR : y ≠ bR)
    (hlevel : G.dist w x = G.dist w y) :
    G.dist x y ≤ 2 := by
  by_cases hzero : G.dist w x = 0
  · have hxw : x = w :=
      ((hconn.dist_eq_zero_iff (u := w) (v := x)).mp hzero).symm
    have hyzero : G.dist w y = 0 := by omega
    have hyw : y = w :=
      ((hconn.dist_eq_zero_iff (u := w) (v := y)).mp hyzero).symm
    subst x
    subst y
    simp
  · have hxAnchor :=
      (IsGeodesic.q2q2PureMass_regular_twoSidedAnchors
        (v := x) hconn hP Ca Cb hCa hCb hothers
        hxaL hxaR hxbL hxbR).2 (by omega)
    have hyAnchor :=
      (IsGeodesic.q2q2PureMass_regular_twoSidedAnchors
        (v := y) hconn hP Ca Cb hCa hCb hothers
        hyaL hyaR hybL hybR).2 (by omega)
    have hsameAnchor : G.dist w x - 1 = G.dist w y - 1 := by omega
    rw [hsameAnchor] at hxAnchor
    have hxDist : G.dist x (P.getVert (G.dist w y - 1)) = 1 :=
      dist_eq_one_iff_adj.mpr hxAnchor.symm
    have hyDist : G.dist (P.getVert (G.dist w y - 1)) y = 1 :=
      dist_eq_one_iff_adj.mpr hyAnchor
    have htri := hconn.dist_triangle
      (u := x) (v := P.getVert (G.dist w y - 1)) (w := y)
    omega

/-- Away from the unique zero-span leaf, a pure-span graph has the ordinary
two-sided corridor anchors at every vertex. -/
theorem IsGeodesic.pureSpan_regular_twoSidedAnchors
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ v z : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P)
    (Cleaf : OffCorridorComponent P)
    (hleaf : offCorridorComponentFinset Cleaf = {z})
    (hothers : ∀ C : OffCorridorComponent P, C ≠ Cleaf →
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2)
    (hvz : v ≠ z) :
    (G.dist w v < P.length →
      G.Adj v (P.getVert (G.dist w v + 1))) ∧
    (0 < G.dist w v →
      G.Adj (P.getVert (G.dist w v - 1)) v) := by
  classical
  by_cases hvSupport : v ∈ P.support
  · have hvEq := IsGeodesic.eq_getVert_of_mem_support_rootDist_eq
      hP hvSupport (k := G.dist w v) rfl
    have hvBound : G.dist w v ≤ P.length := by
      let j := P.support.idxOf v
      have hj : j ≤ P.length := support_idxOf_le_length P hvSupport
      have hget : P.getVert j = v := P.getVert_support_idxOf hvSupport
      have hlevel := IsGeodesic.rootDist_getVert hP hj
      rw [hget] at hlevel
      omega
    constructor
    · intro hvlt
      have hadj := P.adj_getVert_succ (i := G.dist w v) hvlt
      rw [← hvEq] at hadj
      exact hadj
    · intro hvpos
      have hadj := P.adj_getVert_succ (i := G.dist w v - 1) (by omega)
      have hsucc : G.dist w v - 1 + 1 = G.dist w v := by omega
      rw [hsucc, ← hvEq] at hadj
      exact hadj
  · let C := offCorridorComponentOf P v hvSupport
    have hvC : v ∈ offCorridorComponentFinset C :=
      mem_offCorridorComponentOf P hvSupport
    have hCne : C ≠ Cleaf := by
      intro hEq
      have hvLeaf : v ∈ offCorridorComponentFinset Cleaf := by
        simpa [hEq] using hvC
      have hvEq : v = z := by simpa [hleaf] using hvLeaf
      exact hvz hvEq
    obtain ⟨hsize, hspan⟩ := hothers C hCne
    obtain ⟨l, hinterval⟩ :=
      offCorridorInterval_eq_Ico_of_card_eq_two P C hspan
    obtain ⟨c, hset, hlevel, hleft, hright⟩ :=
      IsGeodesic.singleton_spanTwo_geometry hconn hP C l hsize hinterval
    have hvc : v = c := by simpa [hset] using hvC
    subst v
    constructor
    · intro _
      simpa [hlevel] using hright
    · intro _
      simpa [hlevel] using hleft.symm

theorem IsGeodesic.pureSpan_regular_levelAligned
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ x y z : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P)
    (Cleaf : OffCorridorComponent P)
    (hleaf : offCorridorComponentFinset Cleaf = {z})
    (hothers : ∀ C : OffCorridorComponent P, C ≠ Cleaf →
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2)
    (hxz : x ≠ z) (hyz : y ≠ z)
    (hxBound : G.dist w x ≤ P.length)
    (hyBound : G.dist w y ≤ P.length)
    (hlevelEven : Even (Nat.dist (G.dist w x) (G.dist w y)))
    (hlegal : 4 ≤ G.dist x y) :
    G.dist x y = Nat.dist (G.dist w x) (G.dist w y) := by
  have hsame : G.dist w x = G.dist w y → G.dist x y ≤ 2 := by
    intro heq
    by_cases hzero : G.dist w x = 0
    · have hxw : x = w :=
        ((hconn.dist_eq_zero_iff (u := w) (v := x)).mp hzero).symm
      have hyzero : G.dist w y = 0 := by omega
      have hyw : y = w :=
        ((hconn.dist_eq_zero_iff (u := w) (v := y)).mp hyzero).symm
      subst x
      subst y
      simp
    · have hxAnchor :=
        (IsGeodesic.pureSpan_regular_twoSidedAnchors
          (v := x) hconn hP Cleaf hleaf hothers hxz).2 (by omega)
      have hyAnchor :=
        (IsGeodesic.pureSpan_regular_twoSidedAnchors
          (v := y) hconn hP Cleaf hleaf hothers hyz).2 (by omega)
      have hs : G.dist w x - 1 = G.dist w y - 1 := by omega
      rw [hs] at hxAnchor
      have hxDist : G.dist x (P.getVert (G.dist w y - 1)) = 1 :=
        dist_eq_one_iff_adj.mpr hxAnchor.symm
      have hyDist : G.dist (P.getVert (G.dist w y - 1)) y = 1 :=
        dist_eq_one_iff_adj.mpr hyAnchor
      have htri := hconn.dist_triangle
        (u := x) (v := P.getVert (G.dist w y - 1)) (w := y)
      omega
  have hlower := bfsLevel_natDist_le hconn w x y
  rcases lt_trichotomy (G.dist w x) (G.dist w y) with hlt | heq | hgt
  · have heven : Even (G.dist w y - G.dist w x) := by
      simpa [Nat.dist_eq_sub_of_le hlt.le] using hlevelEven
    obtain ⟨q, hq⟩ := heven
    have hgap : G.dist w x + 2 ≤ G.dist w y := by omega
    have hxAnchor :=
      (IsGeodesic.pureSpan_regular_twoSidedAnchors
        (v := x) hconn hP Cleaf hleaf hothers hxz).1 (by omega)
    have hyAnchor :=
      (IsGeodesic.pureSpan_regular_twoSidedAnchors
        (v := y) hconn hP Cleaf hleaf hothers hyz).2 (by omega)
    have hupper := IsGeodesic.dist_le_levelSub_of_adjacent_corridorAnchors
      hconn hP hgap hyBound hxAnchor hyAnchor
    rw [Nat.dist_eq_sub_of_le hlt.le] at hlower ⊢
    omega
  · have hclose := hsame heq
    omega
  · have heven : Even (G.dist w x - G.dist w y) := by
      simpa [Nat.dist_eq_sub_of_le_right hgt.le] using hlevelEven
    obtain ⟨q, hq⟩ := heven
    have hgap : G.dist w y + 2 ≤ G.dist w x := by omega
    have hyAnchor :=
      (IsGeodesic.pureSpan_regular_twoSidedAnchors
        (v := y) hconn hP Cleaf hleaf hothers hyz).1 (by omega)
    have hxAnchor :=
      (IsGeodesic.pureSpan_regular_twoSidedAnchors
        (v := x) hconn hP Cleaf hleaf hothers hxz).2 (by omega)
    have hupper := IsGeodesic.dist_le_levelSub_of_adjacent_corridorAnchors
      hconn hP hgap hxBound hyAnchor hxAnchor
    rw [SimpleGraph.dist_comm] at hupper
    rw [Nat.dist_eq_sub_of_le_right hgt.le] at hlower ⊢
    omega

/-- An unordered pair agrees with two named endpoints. -/
def PairMatches {V : Type*} (x y a b : V) : Prop :=
  (x = a ∧ y = b) ∨ (x = b ∧ y = a)

/-- The only three pair positions at which a saturated size-three block can
lose distance relative to the rooted BFS coordinate. -/
def Q3ExceptionalPair
    {V : Type*} {G : SimpleGraph V} {w x₀ : V}
    (P : G.Walk w x₀) (l : ℕ) (cL cM cR x y : V) : Prop :=
  PairMatches x y (P.getVert (l + 1)) cR ∨
    PairMatches x y (P.getVert (l + 2)) cM ∨
    PairMatches x y (P.getVert (l + 3)) cL

theorem pairMatches_comm {V : Type*} {x y a b : V} :
    PairMatches x y a b ↔ PairMatches y x a b := by
  simp only [PairMatches]
  aesop

theorem dist_eq_of_pairMatches
    {V : Type*} {G : SimpleGraph V} {x y a b : V}
    (h : PairMatches x y a b) :
    G.dist x y = G.dist a b := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact SimpleGraph.dist_comm

theorem sym2_eq_of_pairMatches
    {V : Type*} {x y a b : V} (h : PairMatches x y a b) :
    s(x, y) = s(a, b) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact Sym2.eq_swap

theorem q3ExceptionalPair_comm
    {V : Type*} {G : SimpleGraph V} {w x₀ : V}
    {P : G.Walk w x₀} {l : ℕ} {cL cM cR x y : V} :
    Q3ExceptionalPair P l cL cM cR x y ↔
      Q3ExceptionalPair P l cL cM cR y x := by
  simp only [Q3ExceptionalPair, pairMatches_comm]

/-- If no off-corridor vertex occupies a rooted level, that level consists
only of the corresponding corridor vertex. -/
theorem IsGeodesic.eq_getVert_of_level_of_noOffVertex
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ v : V} {P : G.Walk w x₀}
    (hP : IsGeodesic P) {k : ℕ} (hk : k ≤ P.length)
    (hno : ∀ z ∈ offCorridorFinset P, G.dist w z ≠ k)
    (hv : G.dist w v = k) :
    v = P.getVert k := by
  by_cases hvs : v ∈ P.support
  · exact IsGeodesic.eq_getVert_of_mem_support_rootDist_eq hP hvs hv
  · have hvoff : v ∈ offCorridorFinset P :=
      Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ v, by simpa [supportFinset] using hvs⟩
    exact (hno v hvoff hv).elim

/-- Endpoint-distance bounds supplied by the literal length-four detour
`p_l-cL-cM-cR-p_(l+4)`. -/
theorem IsGeodesic.q3_endpoint_distance_bounds
    {V : Type*} {G : SimpleGraph V} {w x₀ cL cM cR : V}
    {P : G.Walk w x₀} (hconn : G.Connected) (hP : IsGeodesic P)
    {l : ℕ} (hlength : l + 4 ≤ P.length)
    (hLM : G.Adj cL cM) (hMR : G.Adj cM cR)
    (hleft : G.Adj cL (P.getVert l))
    (hright : G.Adj cR (P.getVert (l + 4))) :
    G.dist (P.getVert l) cL = 1 ∧
      G.dist (P.getVert l) cM ≤ 2 ∧
      G.dist (P.getVert l) cR ≤ 3 ∧
      G.dist cL (P.getVert (l + 4)) ≤ 3 ∧
      G.dist cM (P.getVert (l + 4)) ≤ 2 ∧
      G.dist cR (P.getVert (l + 4)) = 1 := by
  have hdL : G.dist (P.getVert l) cL = 1 :=
    dist_eq_one_iff_adj.mpr hleft.symm
  have hdLM : G.dist cL cM = 1 := dist_eq_one_iff_adj.mpr hLM
  have hdMR : G.dist cM cR = 1 := dist_eq_one_iff_adj.mpr hMR
  have hdR : G.dist cR (P.getVert (l + 4)) = 1 :=
    dist_eq_one_iff_adj.mpr hright
  have hL_M := hconn.dist_triangle
    (u := P.getVert l) (v := cL) (w := cM)
  have hL_R₁ := hconn.dist_triangle
    (u := P.getVert l) (v := cM) (w := cR)
  have hCL_R₁ := hconn.dist_triangle
    (u := cL) (v := cM) (w := P.getVert (l + 4))
  have hCM_R := hconn.dist_triangle
    (u := cM) (v := cR) (w := P.getVert (l + 4))
  exact ⟨hdL, by omega, by omega, by omega, by omega, hdR⟩

/-- Endpoint distances for a saturated two-vertex span-three detour. -/
theorem q2_endpoint_distance_bounds
    {V : Type*} {G : SimpleGraph V} {w x₀ cL cR : V}
    {P : G.Walk w x₀} (hconn : G.Connected)
    {l : ℕ} (hLR : G.Adj cL cR)
    (hleft : G.Adj cL (P.getVert l))
    (hright : G.Adj cR (P.getVert (l + 3))) :
    G.dist (P.getVert l) cL = 1 ∧
      G.dist (P.getVert l) cR ≤ 2 ∧
      G.dist cL (P.getVert (l + 3)) ≤ 2 ∧
      G.dist cR (P.getVert (l + 3)) = 1 := by
  have hdL : G.dist (P.getVert l) cL = 1 :=
    dist_eq_one_iff_adj.mpr hleft.symm
  have hdLR : G.dist cL cR = 1 := dist_eq_one_iff_adj.mpr hLR
  have hdR : G.dist cR (P.getVert (l + 3)) = 1 :=
    dist_eq_one_iff_adj.mpr hright
  have hleftR := hconn.dist_triangle
    (u := P.getVert l) (v := cL) (w := cR)
  have hrightL := hconn.dist_triangle
    (u := cL) (v := cR) (w := P.getVert (l + 3))
  exact ⟨hdL, by omega, by omega, hdR⟩

/-- Oriented alignment for a literal saturated size-three block.  Every
same-color legal pair whose rooted level increases is level-aligned, except
possibly at one of the three explicitly named local positions.  At an
exceptional position the true distance is exactly four. -/
theorem IsGeodesic.q3PureMass_oriented_levelAligned_or_candidate
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ x y cL cM cR : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P)
    (Cstar : OffCorridorComponent P) (l : ℕ)
    (hstar : offCorridorComponentFinset Cstar = {cL, cM, cR})
    (hothers : ∀ C : OffCorridorComponent P, C ≠ Cstar →
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2)
    (hlength : l + 4 ≤ P.length)
    (hLM : G.Adj cL cM) (hMR : G.Adj cM cR)
    (hleft : G.Adj cL (P.getVert l))
    (hright : G.Adj cR (P.getVert (l + 4)))
    (hlevelL : G.dist w cL = l + 1)
    (hlevelM : G.dist w cM = l + 2)
    (hlevelR : G.dist w cR = l + 3)
    (hcLoff : cL ∈ offCorridorFinset P)
    (hcMoff : cM ∈ offCorridorFinset P)
    (hcRoff : cR ∈ offCorridorFinset P)
    (hinjective : Set.InjOn (G.dist w) (offCorridorFinset P : Set V))
    (hnoEndpoint : ∀ z ∈ offCorridorFinset P,
      G.dist w z ≠ l ∧ G.dist w z ≠ l + 4)
    (hxBound : G.dist w x ≤ P.length)
    (hyBound : G.dist w y ≤ P.length)
    (hlt : G.dist w x < G.dist w y)
    (hlevelEven : Even (Nat.dist (G.dist w x) (G.dist w y)))
    (hlegal : 4 ≤ G.dist x y) :
    G.dist x y = G.dist w y - G.dist w x ∨
      (G.dist x y = 4 ∧
        Q3ExceptionalPair P l cL cM cR x y) := by
  have hsubEven : Even (G.dist w y - G.dist w x) := by
    simpa [Nat.dist_eq_sub_of_le hlt.le] using hlevelEven
  obtain ⟨q, hq⟩ := hsubEven
  have hgap : G.dist w x + 2 ≤ G.dist w y := by omega
  have hlower := bfsLevel_natDist_le hconn w x y
  rw [Nat.dist_eq_sub_of_le hlt.le] at hlower
  obtain ⟨hdLeftL, hdLeftM, hdLeftR, hdRightL, hdRightM, hdRightR⟩ :=
    IsGeodesic.q3_endpoint_distance_bounds hconn hP hlength
      hLM hMR hleft hright
  have hLMdist : G.dist cL cM = 1 := dist_eq_one_iff_adj.mpr hLM
  have hMRdist : G.dist cM cR = 1 := dist_eq_one_iff_adj.mpr hMR
  have hLRdist : G.dist cL cR ≤ 2 := by
    have htri := hconn.dist_triangle (u := cL) (v := cM) (w := cR)
    omega
  have hCandA : G.dist (P.getVert (l + 1)) cR ≤ 4 := by
    have hcorr := hP.dist_getVert_eq_sub
      (i := l + 1) (j := l + 4) (by omega) hlength
    have htri := hconn.dist_triangle
      (u := P.getVert (l + 1)) (v := P.getVert (l + 4)) (w := cR)
    rw [SimpleGraph.dist_comm] at hdRightR
    omega
  have hCandB : G.dist (P.getVert (l + 2)) cM ≤ 4 := by
    have hcorr := hP.dist_getVert_eq_sub
      (i := l) (j := l + 2) (by omega) (by omega)
    have htri := hconn.dist_triangle
      (u := P.getVert (l + 2)) (v := P.getVert l) (w := cM)
    rw [SimpleGraph.dist_comm] at hcorr
    omega
  have hCandC : G.dist (P.getVert (l + 3)) cL ≤ 4 := by
    have hcorr := hP.dist_getVert_eq_sub
      (i := l + 3) (j := l + 4) (by omega) hlength
    have htri : G.dist cL (P.getVert (l + 3)) ≤
        G.dist cL (P.getVert (l + 4)) +
          G.dist (P.getVert (l + 4)) (P.getVert (l + 3)) :=
      hconn.dist_triangle
        (u := cL) (v := P.getVert (l + 4)) (w := P.getVert (l + 3))
    have hcorr' : G.dist (P.getVert (l + 4)) (P.getVert (l + 3)) = 1 := by
      simpa [SimpleGraph.dist_comm] using hcorr
    rw [SimpleGraph.dist_comm]
    omega
  by_cases hxL : x = cL
  · subst x
    have hyL : y ≠ cL := by intro h; subst y; omega
    have hyM : y ≠ cM := by intro h; subst y; omega
    have hyR : y ≠ cR := by
      intro h
      subst y
      omega
    have hyBack :=
      (IsGeodesic.q3PureMass_regular_twoSidedAnchors
        (v := y) hconn hP Cstar hstar hothers hyL hyM hyR).2 (by omega)
    by_cases hnear : G.dist w y = l + 3
    · have hyCases := IsGeodesic.eq_getVert_or_eq_offVertex_of_level
        hP hinjective hcRoff hlevelR hnear
      rcases hyCases with hy | hy
      · right
        have hd : G.dist cL y = 4 := by
          have hleg : 4 ≤ G.dist (P.getVert (l + 3)) cL := by
            simpa [hy, SimpleGraph.dist_comm] using hlegal
          rw [hy, SimpleGraph.dist_comm]
          omega
        refine ⟨hd, Or.inr (Or.inr ?_)⟩
        exact Or.inr ⟨rfl, hy⟩
      · exact (hyR hy).elim
    · have hfar : l + 5 ≤ G.dist w y := by omega
      have hupper := IsGeodesic.dist_le_levelSub_of_rightEndpointRoute
        (z := cL) (y := y) hconn hP
        (a := l + 1) (e := l + 4) (b := G.dist w y)
        (by omega) hfar hyBound (by omega) hyBack
      left
      omega
  · by_cases hxM : x = cM
    · subst x
      have hyL : y ≠ cL := by intro h; subst y; omega
      have hyM : y ≠ cM := by intro h; subst y; omega
      have hyR : y ≠ cR := by intro h; subst y; omega
      by_cases hnear : G.dist w y = l + 4
      · have hy : y = P.getVert (l + 4) :=
          IsGeodesic.eq_getVert_of_level_of_noOffVertex
            hP hlength (fun z hz => (hnoEndpoint z hz).2) hnear
        have hupper : G.dist cM y ≤ 2 := by simpa [hy] using hdRightM
        left
        omega
      · have hfar : l + 6 ≤ G.dist w y := by omega
        have hyBack :=
          (IsGeodesic.q3PureMass_regular_twoSidedAnchors
            (v := y) hconn hP Cstar hstar hothers hyL hyM hyR).2 (by omega)
        have hupper := IsGeodesic.dist_le_levelSub_of_rightEndpointRoute
          (z := cM) (y := y) hconn hP
          (a := l + 2) (e := l + 4) (b := G.dist w y)
          (by omega) (by omega) hyBound (by omega) hyBack
        left
        omega
    · by_cases hxR : x = cR
      · subst x
        have hyL : y ≠ cL := by intro h; subst y; omega
        have hyM : y ≠ cM := by intro h; subst y; omega
        have hyR : y ≠ cR := by intro h; subst y; omega
        have hyBack :=
          (IsGeodesic.q3PureMass_regular_twoSidedAnchors
            (v := y) hconn hP Cstar hstar hothers hyL hyM hyR).2 (by omega)
        have hupper :=
          IsGeodesic.dist_le_levelSub_of_adjacent_corridorAnchors
            hconn hP (a := l + 3) (b := G.dist w y)
            (by omega) hyBound hright hyBack
        left
        omega
      · by_cases hyL : y = cL
        · subst y
          have hxForward :=
            (IsGeodesic.q3PureMass_regular_twoSidedAnchors
              (v := x) hconn hP Cstar hstar hothers hxL hxM hxR).1 (by omega)
          have hupper := IsGeodesic.dist_le_levelSub_of_leftEndpointRoute
            (x := x) (z := cL) hconn hP
            (a := G.dist w x) (e := l) (b := l + 1)
            (by omega) (by omega) (by omega) hxForward (by omega)
          left
          omega
        · by_cases hyM : y = cM
          · subst y
            by_cases hnear : G.dist w x = l
            · have hx : x = P.getVert l :=
                IsGeodesic.eq_getVert_of_level_of_noOffVertex
                  hP (by omega) (fun z hz => (hnoEndpoint z hz).1) hnear
              have hupper : G.dist x cM ≤ 2 := by simpa [hx] using hdLeftM
              left
              omega
            · have hxForward :=
                (IsGeodesic.q3PureMass_regular_twoSidedAnchors
                  (v := x) hconn hP Cstar hstar hothers hxL hxM hxR).1 (by omega)
              have hupper := IsGeodesic.dist_le_levelSub_of_leftEndpointRoute
                (x := x) (z := cM) hconn hP
                (a := G.dist w x) (e := l) (b := l + 2)
                (by omega) (by omega) (by omega) hxForward (by omega)
              left
              omega
          · by_cases hyR : y = cR
            · subst y
              by_cases hnear : G.dist w x = l + 1
              · have hxCases := IsGeodesic.eq_getVert_or_eq_offVertex_of_level
                  hP hinjective hcLoff hlevelL hnear
                rcases hxCases with hx | hx
                · right
                  have hleg : 4 ≤ G.dist (P.getVert (l + 1)) cR := by
                    simpa [hx] using hlegal
                  have hd : G.dist x cR = 4 := by
                    rw [hx]
                    omega
                  refine ⟨hd, Or.inl ?_⟩
                  exact Or.inl ⟨hx, rfl⟩
                · exact (hxL hx).elim
              · have hxForward :=
                  (IsGeodesic.q3PureMass_regular_twoSidedAnchors
                    (v := x) hconn hP Cstar hstar hothers hxL hxM hxR).1 (by omega)
                have hupper := IsGeodesic.dist_le_levelSub_of_leftEndpointRoute
                  (x := x) (z := cR) hconn hP
                  (a := G.dist w x) (e := l) (b := l + 3)
                  (by omega) (by omega) (by omega) hxForward (by omega)
                left
                omega
            · have hxForward :=
                (IsGeodesic.q3PureMass_regular_twoSidedAnchors
                  (v := x) hconn hP Cstar hstar hothers hxL hxM hxR).1 (by omega)
              have hyBack :=
                (IsGeodesic.q3PureMass_regular_twoSidedAnchors
                  (v := y) hconn hP Cstar hstar hothers hyL hyM hyR).2 (by omega)
              have hupper :=
                IsGeodesic.dist_le_levelSub_of_adjacent_corridorAnchors
                  hconn hP (a := G.dist w x) (b := G.dist w y)
                  hgap hyBound hxForward hyBack
              left
              omega

/-- Unoriented form of the q3 alignment classification.  Same-level legal
pairs contribute only the central candidate; reversing a pair preserves the
three-candidate predicate. -/
theorem IsGeodesic.q3PureMass_levelAligned_or_candidate
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ x y cL cM cR : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P)
    (Cstar : OffCorridorComponent P) (l : ℕ)
    (hstar : offCorridorComponentFinset Cstar = {cL, cM, cR})
    (hothers : ∀ C : OffCorridorComponent P, C ≠ Cstar →
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2)
    (hlength : l + 4 ≤ P.length)
    (hLM : G.Adj cL cM) (hMR : G.Adj cM cR)
    (hleft : G.Adj cL (P.getVert l))
    (hright : G.Adj cR (P.getVert (l + 4)))
    (hlevelL : G.dist w cL = l + 1)
    (hlevelM : G.dist w cM = l + 2)
    (hlevelR : G.dist w cR = l + 3)
    (hcLoff : cL ∈ offCorridorFinset P)
    (hcMoff : cM ∈ offCorridorFinset P)
    (hcRoff : cR ∈ offCorridorFinset P)
    (hinjective : Set.InjOn (G.dist w) (offCorridorFinset P : Set V))
    (hnoEndpoint : ∀ z ∈ offCorridorFinset P,
      G.dist w z ≠ l ∧ G.dist w z ≠ l + 4)
    (hxBound : G.dist w x ≤ P.length)
    (hyBound : G.dist w y ≤ P.length)
    (hlevelEven : Even (Nat.dist (G.dist w x) (G.dist w y)))
    (hlegal : 4 ≤ G.dist x y) :
    G.dist x y = Nat.dist (G.dist w x) (G.dist w y) ∨
      (G.dist x y = 4 ∧
        Q3ExceptionalPair P l cL cM cR x y) := by
  have hcloseL : G.dist cL (P.getVert (l + 1)) ≤ 2 := by
    have hleftDist : G.dist cL (P.getVert l) = 1 :=
      dist_eq_one_iff_adj.mpr hleft
    have hcorr := hP.dist_getVert_eq_sub
      (i := l) (j := l + 1) (by omega) (by omega)
    have htri := hconn.dist_triangle
      (u := cL) (v := P.getVert l) (w := P.getVert (l + 1))
    omega
  have hcloseR : G.dist cR (P.getVert (l + 3)) ≤ 2 := by
    have hrightDist : G.dist cR (P.getVert (l + 4)) = 1 :=
      dist_eq_one_iff_adj.mpr hright
    have hcorr := hP.dist_getVert_eq_sub
      (i := l + 3) (j := l + 4) (by omega) hlength
    have htri := hconn.dist_triangle
      (u := cR) (v := P.getVert (l + 4)) (w := P.getVert (l + 3))
    rw [SimpleGraph.dist_comm] at hcorr
    omega
  have hCandB : G.dist (P.getVert (l + 2)) cM ≤ 4 := by
    obtain ⟨_hdLeftL, hdLeftM, _hdLeftR, _hdRightL,
        _hdRightM, _hdRightR⟩ :=
      IsGeodesic.q3_endpoint_distance_bounds hconn hP hlength
        hLM hMR hleft hright
    have hcorr := hP.dist_getVert_eq_sub
      (i := l) (j := l + 2) (by omega) (by omega)
    have htri := hconn.dist_triangle
      (u := P.getVert (l + 2)) (v := P.getVert l) (w := cM)
    rw [SimpleGraph.dist_comm] at hcorr
    omega
  rcases lt_trichotomy (G.dist w x) (G.dist w y) with hlt | heq | hgt
  · obtain haligned | hexception :=
      IsGeodesic.q3PureMass_oriented_levelAligned_or_candidate
        hconn hP Cstar l hstar hothers hlength hLM hMR hleft hright
        hlevelL hlevelM hlevelR hcLoff hcMoff hcRoff hinjective
        hnoEndpoint hxBound hyBound hlt hlevelEven hlegal
    · left
      rw [Nat.dist_eq_sub_of_le hlt.le]
      exact haligned
    · exact Or.inr hexception
  · by_cases hxL : x = cL
    · subst x
      have hyLevel : G.dist w y = l + 1 := by omega
      have hyCases := IsGeodesic.eq_getVert_or_eq_offVertex_of_level
        hP hinjective hcLoff hlevelL hyLevel
      rcases hyCases with hy | hy
      · have hclose : G.dist cL y ≤ 2 := by simpa [hy] using hcloseL
        omega
      · subst y
        simp at hlegal
    · by_cases hxM : x = cM
      · subst x
        have hyLevel : G.dist w y = l + 2 := by omega
        have hyCases := IsGeodesic.eq_getVert_or_eq_offVertex_of_level
          hP hinjective hcMoff hlevelM hyLevel
        rcases hyCases with hy | hy
        · right
          have hleg : 4 ≤ G.dist (P.getVert (l + 2)) cM := by
            simpa [hy, SimpleGraph.dist_comm] using hlegal
          have hd : G.dist cM y = 4 := by
            rw [hy, SimpleGraph.dist_comm]
            omega
          refine ⟨hd, Or.inr (Or.inl ?_)⟩
          exact Or.inr ⟨rfl, hy⟩
        · subst y
          simp at hlegal
      · by_cases hxR : x = cR
        · subst x
          have hyLevel : G.dist w y = l + 3 := by omega
          have hyCases := IsGeodesic.eq_getVert_or_eq_offVertex_of_level
            hP hinjective hcRoff hlevelR hyLevel
          rcases hyCases with hy | hy
          · have hclose : G.dist cR y ≤ 2 := by simpa [hy] using hcloseR
            omega
          · subst y
            simp at hlegal
        · by_cases hyL : y = cL
          · subst y
            have hxLevel : G.dist w x = l + 1 := by omega
            have hxCases := IsGeodesic.eq_getVert_or_eq_offVertex_of_level
              hP hinjective hcLoff hlevelL hxLevel
            rcases hxCases with hx | hx
            · have hclose : G.dist x cL ≤ 2 := by
                rw [hx, SimpleGraph.dist_comm]
                exact hcloseL
              omega
            · exact (hxL hx).elim
          · by_cases hyM : y = cM
            · subst y
              have hxLevel : G.dist w x = l + 2 := by omega
              have hxCases := IsGeodesic.eq_getVert_or_eq_offVertex_of_level
                hP hinjective hcMoff hlevelM hxLevel
              rcases hxCases with hx | hx
              · right
                have hleg : 4 ≤ G.dist (P.getVert (l + 2)) cM := by
                  simpa [hx] using hlegal
                have hd : G.dist x cM = 4 := by rw [hx]; omega
                refine ⟨hd, Or.inr (Or.inl ?_)⟩
                exact Or.inl ⟨hx, rfl⟩
              · exact (hxM hx).elim
            · by_cases hyR : y = cR
              · subst y
                have hxLevel : G.dist w x = l + 3 := by omega
                have hxCases := IsGeodesic.eq_getVert_or_eq_offVertex_of_level
                  hP hinjective hcRoff hlevelR hxLevel
                rcases hxCases with hx | hx
                · have hclose : G.dist x cR ≤ 2 := by
                    simpa [hx, SimpleGraph.dist_comm] using hcloseR
                  omega
                · exact (hxR hx).elim
              · have hclose :=
                  IsGeodesic.q3PureMass_regular_sameLevel_dist_le_two
                    hconn hP Cstar hstar hothers hxL hxM hxR
                    hyL hyM hyR heq
                omega
  · have hlevelEven' :
        Even (Nat.dist (G.dist w y) (G.dist w x)) := by
      simpa [Nat.dist_comm] using hlevelEven
    have hlegal' : 4 ≤ G.dist y x := by
      simpa [SimpleGraph.dist_comm] using hlegal
    obtain haligned | hexception :=
      IsGeodesic.q3PureMass_oriented_levelAligned_or_candidate
        hconn hP Cstar l hstar hothers hlength hLM hMR hleft hright
        hlevelL hlevelM hlevelR hcLoff hcMoff hcRoff hinjective
        hnoEndpoint hyBound hxBound hgt hlevelEven' hlegal'
    · left
      rw [SimpleGraph.dist_comm, Nat.dist_eq_sub_of_le_right hgt.le]
      exact haligned
    · right
      refine ⟨?_, (q3ExceptionalPair_comm).mpr hexception.2⟩
      simpa [SimpleGraph.dist_comm] using hexception.1

/-- Oriented alignment in the pure-mass `q2+q2` geometry.  The two
span-three blocks are ordered from left to right.  Their one-sided special
vertices route through the appropriate block endpoint; parity handles the
only two near-endpoint cases. -/
theorem IsGeodesic.q2q2PureMass_oriented_levelAligned
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ x y aL aR bL bR : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P)
    (Ca Cb : OffCorridorComponent P) (la lb : ℕ)
    (hCa : offCorridorComponentFinset Ca = {aL, aR})
    (hCb : offCorridorComponentFinset Cb = {bL, bR})
    (hothers : ∀ C : OffCorridorComponent P, C ≠ Ca → C ≠ Cb →
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2)
    (horder : la + 3 ≤ lb) (hlength : lb + 3 ≤ P.length)
    (hALR : G.Adj aL aR) (hBLR : G.Adj bL bR)
    (hAleft : G.Adj aL (P.getVert la))
    (hAright : G.Adj aR (P.getVert (la + 3)))
    (hBleft : G.Adj bL (P.getVert lb))
    (hBright : G.Adj bR (P.getVert (lb + 3)))
    (hlevelAL : G.dist w aL = la + 1)
    (hlevelAR : G.dist w aR = la + 2)
    (hlevelBL : G.dist w bL = lb + 1)
    (hlevelBR : G.dist w bR = lb + 2)
    (hnoAEndpoint : ∀ z ∈ offCorridorFinset P,
      G.dist w z ≠ la ∧ G.dist w z ≠ la + 3)
    (hnoBEndpoint : ∀ z ∈ offCorridorFinset P,
      G.dist w z ≠ lb ∧ G.dist w z ≠ lb + 3)
    (hxBound : G.dist w x ≤ P.length)
    (hyBound : G.dist w y ≤ P.length)
    (hlt : G.dist w x < G.dist w y)
    (hlevelEven : Even (Nat.dist (G.dist w x) (G.dist w y)))
    (hlegal : 4 ≤ G.dist x y) :
    G.dist x y = G.dist w y - G.dist w x := by
  have hsubEven : Even (G.dist w y - G.dist w x) := by
    simpa [Nat.dist_eq_sub_of_le hlt.le] using hlevelEven
  obtain ⟨q, hq⟩ := hsubEven
  have hgap : G.dist w x + 2 ≤ G.dist w y := by omega
  have hlower := bfsLevel_natDist_le hconn w x y
  rw [Nat.dist_eq_sub_of_le hlt.le] at hlower
  obtain ⟨hALeftL, hALeftR, hARightL, hARightR⟩ :=
    q2_endpoint_distance_bounds hconn hALR hAleft hAright
  obtain ⟨hBLeftL, hBLeftR, hBRightL, hBRightR⟩ :=
    q2_endpoint_distance_bounds hconn hBLR hBleft hBright
  have hAtoBL (hxCoord : G.dist w x ≤ la + 3)
      (hxExit : G.dist x (P.getVert (la + 3)) ≤
      la + 3 - G.dist w x) : G.dist x bL ≤ G.dist w bL - G.dist w x := by
    have hupper := IsGeodesic.dist_le_levelSub_of_twoEndpointRoutes
      (x := x) (y := bL) hconn hP
      (a := G.dist w x) (e := la + 3) (f := lb) (b := lb + 1)
      hxCoord horder (by omega) (by omega) hxExit (by omega)
    omega
  have hAtoBR (hxCoord : G.dist w x ≤ la + 3)
      (hxExit : G.dist x (P.getVert (la + 3)) ≤
      la + 3 - G.dist w x) : G.dist x bR ≤ G.dist w bR - G.dist w x := by
    have hupper := IsGeodesic.dist_le_levelSub_of_twoEndpointRoutes
      (x := x) (y := bR) hconn hP
      (a := G.dist w x) (e := la + 3) (f := lb) (b := lb + 2)
      hxCoord horder (by omega) (by omega) hxExit (by omega)
    omega
  by_cases hxaL : x = aL
  · subst x
    have hyaL : y ≠ aL := by intro h; subst y; omega
    have hyaR : y ≠ aR := by intro h; subst y; omega
    by_cases hybL : y = bL
    · subst y
      have hupper := hAtoBL (by omega) (by omega)
      omega
    · by_cases hybR : y = bR
      · subst y
        have hupper := hAtoBR (by omega) (by omega)
        omega
      · by_cases hnear : G.dist w y = la + 3
        · have hy : y = P.getVert (la + 3) :=
            IsGeodesic.eq_getVert_of_level_of_noOffVertex
              hP (by omega) (fun z hz => (hnoAEndpoint z hz).2) hnear
          have hupper : G.dist aL y ≤ 2 := by simpa [hy] using hARightL
          omega
        · have hfar : la + 5 ≤ G.dist w y := by omega
          have hyBack :=
            (IsGeodesic.q2q2PureMass_regular_twoSidedAnchors
              (v := y) hconn hP Ca Cb hCa hCb hothers
              hyaL hyaR hybL hybR).2 (by omega)
          have hyDist : G.dist (P.getVert (G.dist w y - 1)) y = 1 :=
            dist_eq_one_iff_adj.mpr hyBack
          have hupper := IsGeodesic.dist_le_levelSub_of_twoEndpointRoutes
            (x := aL) (y := y) hconn hP
            (a := la + 1) (e := la + 3)
            (f := G.dist w y - 1) (b := G.dist w y)
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          omega
  · by_cases hxaR : x = aR
    · subst x
      have hyaL : y ≠ aL := by intro h; subst y; omega
      have hyaR : y ≠ aR := by intro h; subst y; omega
      by_cases hybL : y = bL
      · subst y
        have hupper := hAtoBL (by omega) (by omega)
        omega
      · by_cases hybR : y = bR
        · subst y
          have hupper := hAtoBR (by omega) (by omega)
          omega
        · have hyBack :=
            (IsGeodesic.q2q2PureMass_regular_twoSidedAnchors
              (v := y) hconn hP Ca Cb hCa hCb hothers
              hyaL hyaR hybL hybR).2 (by omega)
          have hyDist : G.dist (P.getVert (G.dist w y - 1)) y = 1 :=
            dist_eq_one_iff_adj.mpr hyBack
          have hupper := IsGeodesic.dist_le_levelSub_of_twoEndpointRoutes
            (x := aR) (y := y) hconn hP
            (a := la + 2) (e := la + 3)
            (f := G.dist w y - 1) (b := G.dist w y)
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          omega
    · by_cases hxbL : x = bL
      · subst x
        have hyaL : y ≠ aL := by intro h; subst y; omega
        have hyaR : y ≠ aR := by intro h; subst y; omega
        have hybL : y ≠ bL := by intro h; subst y; omega
        have hybR : y ≠ bR := by intro h; subst y; omega
        by_cases hnear : G.dist w y = lb + 3
        · have hy : y = P.getVert (lb + 3) :=
            IsGeodesic.eq_getVert_of_level_of_noOffVertex
              hP hlength (fun z hz => (hnoBEndpoint z hz).2) hnear
          have hupper : G.dist bL y ≤ 2 := by simpa [hy] using hBRightL
          omega
        · have hyBack :=
            (IsGeodesic.q2q2PureMass_regular_twoSidedAnchors
              (v := y) hconn hP Ca Cb hCa hCb hothers
              hyaL hyaR hybL hybR).2 (by omega)
          have hyDist : G.dist (P.getVert (G.dist w y - 1)) y = 1 :=
            dist_eq_one_iff_adj.mpr hyBack
          have hupper := IsGeodesic.dist_le_levelSub_of_twoEndpointRoutes
            (x := bL) (y := y) hconn hP
            (a := lb + 1) (e := lb + 3)
            (f := G.dist w y - 1) (b := G.dist w y)
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          omega
      · by_cases hxbR : x = bR
        · subst x
          have hyaL : y ≠ aL := by intro h; subst y; omega
          have hyaR : y ≠ aR := by intro h; subst y; omega
          have hybL : y ≠ bL := by intro h; subst y; omega
          have hybR : y ≠ bR := by intro h; subst y; omega
          have hyBack :=
            (IsGeodesic.q2q2PureMass_regular_twoSidedAnchors
              (v := y) hconn hP Ca Cb hCa hCb hothers
              hyaL hyaR hybL hybR).2 (by omega)
          have hyDist : G.dist (P.getVert (G.dist w y - 1)) y = 1 :=
            dist_eq_one_iff_adj.mpr hyBack
          have hupper := IsGeodesic.dist_le_levelSub_of_twoEndpointRoutes
            (x := bR) (y := y) hconn hP
            (a := lb + 2) (e := lb + 3)
            (f := G.dist w y - 1) (b := G.dist w y)
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          omega
        · by_cases hyaL : y = aL
          · subst y
            have hxForward :=
              (IsGeodesic.q2q2PureMass_regular_twoSidedAnchors
                (v := x) hconn hP Ca Cb hCa hCb hothers
                hxaL hxaR hxbL hxbR).1 (by omega)
            have hxDist : G.dist x (P.getVert (G.dist w x + 1)) = 1 :=
              dist_eq_one_iff_adj.mpr hxForward
            have hupper := IsGeodesic.dist_le_levelSub_of_twoEndpointRoutes
              (x := x) (y := aL) hconn hP
              (a := G.dist w x) (e := G.dist w x + 1)
              (f := la) (b := la + 1)
              (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            omega
          · by_cases hyaR : y = aR
            · subst y
              by_cases hnear : G.dist w x = la
              · have hx : x = P.getVert la :=
                  IsGeodesic.eq_getVert_of_level_of_noOffVertex
                    hP (by omega) (fun z hz => (hnoAEndpoint z hz).1) hnear
                have hupper : G.dist x aR ≤ 2 := by simpa [hx] using hALeftR
                omega
              · have hxForward :=
                  (IsGeodesic.q2q2PureMass_regular_twoSidedAnchors
                    (v := x) hconn hP Ca Cb hCa hCb hothers
                    hxaL hxaR hxbL hxbR).1 (by omega)
                have hxDist : G.dist x (P.getVert (G.dist w x + 1)) = 1 :=
                  dist_eq_one_iff_adj.mpr hxForward
                have hupper := IsGeodesic.dist_le_levelSub_of_twoEndpointRoutes
                  (x := x) (y := aR) hconn hP
                  (a := G.dist w x) (e := G.dist w x + 1)
                  (f := la) (b := la + 2)
                  (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                omega
            · by_cases hybL : y = bL
              · subst y
                have hxForward :=
                  (IsGeodesic.q2q2PureMass_regular_twoSidedAnchors
                    (v := x) hconn hP Ca Cb hCa hCb hothers
                    hxaL hxaR hxbL hxbR).1 (by omega)
                have hxDist : G.dist x (P.getVert (G.dist w x + 1)) = 1 :=
                  dist_eq_one_iff_adj.mpr hxForward
                have hupper := IsGeodesic.dist_le_levelSub_of_twoEndpointRoutes
                  (x := x) (y := bL) hconn hP
                  (a := G.dist w x) (e := G.dist w x + 1)
                  (f := lb) (b := lb + 1)
                  (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                omega
              · by_cases hybR : y = bR
                · subst y
                  by_cases hnear : G.dist w x = lb
                  · have hx : x = P.getVert lb :=
                      IsGeodesic.eq_getVert_of_level_of_noOffVertex
                        hP (by omega) (fun z hz => (hnoBEndpoint z hz).1) hnear
                    have hupper : G.dist x bR ≤ 2 := by simpa [hx] using hBLeftR
                    omega
                  · have hxForward :=
                      (IsGeodesic.q2q2PureMass_regular_twoSidedAnchors
                        (v := x) hconn hP Ca Cb hCa hCb hothers
                        hxaL hxaR hxbL hxbR).1 (by omega)
                    have hxDist : G.dist x (P.getVert (G.dist w x + 1)) = 1 :=
                      dist_eq_one_iff_adj.mpr hxForward
                    have hupper := IsGeodesic.dist_le_levelSub_of_twoEndpointRoutes
                      (x := x) (y := bR) hconn hP
                      (a := G.dist w x) (e := G.dist w x + 1)
                      (f := lb) (b := lb + 2)
                      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                    omega
                · have hxForward :=
                    (IsGeodesic.q2q2PureMass_regular_twoSidedAnchors
                      (v := x) hconn hP Ca Cb hCa hCb hothers
                      hxaL hxaR hxbL hxbR).1 (by omega)
                  have hyBack :=
                    (IsGeodesic.q2q2PureMass_regular_twoSidedAnchors
                      (v := y) hconn hP Ca Cb hCa hCb hothers
                      hyaL hyaR hybL hybR).2 (by omega)
                  have hupper :=
                    IsGeodesic.dist_le_levelSub_of_adjacent_corridorAnchors
                      hconn hP hgap hyBound hxForward hyBack
                  omega

/-- Complete level alignment for two ordered saturated size-two blocks. -/
theorem IsGeodesic.q2q2PureMass_levelAligned
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ x y aL aR bL bR : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P)
    (Ca Cb : OffCorridorComponent P) (la lb : ℕ)
    (hCa : offCorridorComponentFinset Ca = {aL, aR})
    (hCb : offCorridorComponentFinset Cb = {bL, bR})
    (hothers : ∀ C : OffCorridorComponent P, C ≠ Ca → C ≠ Cb →
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2)
    (horder : la + 3 ≤ lb) (hlength : lb + 3 ≤ P.length)
    (hALR : G.Adj aL aR) (hBLR : G.Adj bL bR)
    (hAleft : G.Adj aL (P.getVert la))
    (hAright : G.Adj aR (P.getVert (la + 3)))
    (hBleft : G.Adj bL (P.getVert lb))
    (hBright : G.Adj bR (P.getVert (lb + 3)))
    (hlevelAL : G.dist w aL = la + 1)
    (hlevelAR : G.dist w aR = la + 2)
    (hlevelBL : G.dist w bL = lb + 1)
    (hlevelBR : G.dist w bR = lb + 2)
    (haLoff : aL ∈ offCorridorFinset P)
    (haRoff : aR ∈ offCorridorFinset P)
    (hbLoff : bL ∈ offCorridorFinset P)
    (hbRoff : bR ∈ offCorridorFinset P)
    (hinjective : Set.InjOn (G.dist w) (offCorridorFinset P : Set V))
    (hnoAEndpoint : ∀ z ∈ offCorridorFinset P,
      G.dist w z ≠ la ∧ G.dist w z ≠ la + 3)
    (hnoBEndpoint : ∀ z ∈ offCorridorFinset P,
      G.dist w z ≠ lb ∧ G.dist w z ≠ lb + 3)
    (hxBound : G.dist w x ≤ P.length)
    (hyBound : G.dist w y ≤ P.length)
    (hlevelEven : Even (Nat.dist (G.dist w x) (G.dist w y)))
    (hlegal : 4 ≤ G.dist x y) :
    G.dist x y = Nat.dist (G.dist w x) (G.dist w y) := by
  obtain ⟨hALeftL, _hALeftR, _hARightL, hARightR⟩ :=
    q2_endpoint_distance_bounds hconn hALR hAleft hAright
  obtain ⟨hBLeftL, _hBLeftR, _hBRightL, hBRightR⟩ :=
    q2_endpoint_distance_bounds hconn hBLR hBleft hBright
  have hcloseAL : G.dist aL (P.getVert (la + 1)) ≤ 2 := by
    have hcorr := hP.dist_getVert_eq_sub
      (i := la) (j := la + 1) (by omega) (by omega)
    have htri := hconn.dist_triangle
      (u := aL) (v := P.getVert la) (w := P.getVert (la + 1))
    rw [SimpleGraph.dist_comm] at hALeftL
    omega
  have hcloseAR : G.dist aR (P.getVert (la + 2)) ≤ 2 := by
    have hcorr := hP.dist_getVert_eq_sub
      (i := la + 2) (j := la + 3) (by omega) (by omega)
    have htri := hconn.dist_triangle
      (u := aR) (v := P.getVert (la + 3)) (w := P.getVert (la + 2))
    rw [SimpleGraph.dist_comm] at hcorr
    omega
  have hcloseBL : G.dist bL (P.getVert (lb + 1)) ≤ 2 := by
    have hcorr := hP.dist_getVert_eq_sub
      (i := lb) (j := lb + 1) (by omega) (by omega)
    have htri := hconn.dist_triangle
      (u := bL) (v := P.getVert lb) (w := P.getVert (lb + 1))
    rw [SimpleGraph.dist_comm] at hBLeftL
    omega
  have hcloseBR : G.dist bR (P.getVert (lb + 2)) ≤ 2 := by
    have hcorr := hP.dist_getVert_eq_sub
      (i := lb + 2) (j := lb + 3) (by omega) hlength
    have htri := hconn.dist_triangle
      (u := bR) (v := P.getVert (lb + 3)) (w := P.getVert (lb + 2))
    rw [SimpleGraph.dist_comm] at hcorr
    omega
  rcases lt_trichotomy (G.dist w x) (G.dist w y) with hlt | heq | hgt
  · have h := IsGeodesic.q2q2PureMass_oriented_levelAligned
      hconn hP Ca Cb la lb hCa hCb hothers horder hlength
      hALR hBLR hAleft hAright hBleft hBright
      hlevelAL hlevelAR hlevelBL hlevelBR hnoAEndpoint hnoBEndpoint
      hxBound hyBound hlt hlevelEven hlegal
    rw [Nat.dist_eq_sub_of_le hlt.le]
    exact h

  · by_cases hxaL : x = aL
    · subst x
      have hyLevel : G.dist w y = la + 1 := by omega
      have hclose := IsGeodesic.dist_namedOffVertex_sameLevel_le_two
        hP hinjective haLoff hlevelAL hyLevel hcloseAL
      omega
    · by_cases hxaR : x = aR
      · subst x
        have hyLevel : G.dist w y = la + 2 := by omega
        have hclose := IsGeodesic.dist_namedOffVertex_sameLevel_le_two
          hP hinjective haRoff hlevelAR hyLevel hcloseAR
        omega
      · by_cases hxbL : x = bL
        · subst x
          have hyLevel : G.dist w y = lb + 1 := by omega
          have hclose := IsGeodesic.dist_namedOffVertex_sameLevel_le_two
            hP hinjective hbLoff hlevelBL hyLevel hcloseBL
          omega
        · by_cases hxbR : x = bR
          · subst x
            have hyLevel : G.dist w y = lb + 2 := by omega
            have hclose := IsGeodesic.dist_namedOffVertex_sameLevel_le_two
              hP hinjective hbRoff hlevelBR hyLevel hcloseBR
            omega
          · by_cases hyaL : y = aL
            · subst y
              have hxLevel : G.dist w x = la + 1 := by omega
              have hclose := IsGeodesic.dist_namedOffVertex_sameLevel_le_two
                hP hinjective haLoff hlevelAL hxLevel hcloseAL
              rw [SimpleGraph.dist_comm] at hclose
              omega
            · by_cases hyaR : y = aR
              · subst y
                have hxLevel : G.dist w x = la + 2 := by omega
                have hclose := IsGeodesic.dist_namedOffVertex_sameLevel_le_two
                  hP hinjective haRoff hlevelAR hxLevel hcloseAR
                rw [SimpleGraph.dist_comm] at hclose
                omega
              · by_cases hybL : y = bL
                · subst y
                  have hxLevel : G.dist w x = lb + 1 := by omega
                  have hclose := IsGeodesic.dist_namedOffVertex_sameLevel_le_two
                    hP hinjective hbLoff hlevelBL hxLevel hcloseBL
                  rw [SimpleGraph.dist_comm] at hclose
                  omega
                · by_cases hybR : y = bR
                  · subst y
                    have hxLevel : G.dist w x = lb + 2 := by omega
                    have hclose := IsGeodesic.dist_namedOffVertex_sameLevel_le_two
                      hP hinjective hbRoff hlevelBR hxLevel hcloseBR
                    rw [SimpleGraph.dist_comm] at hclose
                    omega
                  · have hclose :=
                      IsGeodesic.q2q2PureMass_regular_sameLevel_dist_le_two
                        hconn hP Ca Cb hCa hCb hothers
                        hxaL hxaR hxbL hxbR hyaL hyaR hybL hybR heq
                    omega
  · have hlevelEven' : Even (Nat.dist (G.dist w y) (G.dist w x)) := by
      simpa [Nat.dist_comm] using hlevelEven
    have hlegal' : 4 ≤ G.dist y x := by
      simpa [SimpleGraph.dist_comm] using hlegal
    have h := IsGeodesic.q2q2PureMass_oriented_levelAligned
      hconn hP Ca Cb la lb hCa hCb hothers horder hlength
      hALR hBLR hAleft hAright hBleft hBright
      hlevelAL hlevelAR hlevelBL hlevelBR hnoAEndpoint hnoBEndpoint
      hyBound hxBound hgt hlevelEven' hlegal'
    rw [SimpleGraph.dist_comm, Nat.dist_eq_sub_of_le_right hgt.le]
    exact h

/-- In a connected bipartite graph, adjacent vertices occupy consecutive
rooted BFS levels. -/
theorem Coloring.adj_rootDist_natDist_eq_one
    {V : Type*} {G : SimpleGraph V} {w u v : V}
    (hconn : G.Connected) (color : G.Coloring Bool) (huv : G.Adj u v) :
    Nat.dist (G.dist w u) (G.dist w v) = 1 := by
  have hupper := bfsLevel_natDist_le hconn w u v
  have hdistOne : G.dist u v = 1 := dist_eq_one_iff_adj.mpr huv
  have hlevelsNe : G.dist w u ≠ G.dist w v := by
    intro heq
    obtain ⟨Qu, hQu⟩ := hconn.exists_walk_length_eq_dist w u
    obtain ⟨Qv, hQv⟩ := hconn.exists_walk_length_eq_dist w v
    let W := Qu.reverse.append Qv
    have hEven : Even W.length := by
      refine ⟨G.dist w u, ?_⟩
      simp only [W, Walk.length_append, Walk.length_reverse, hQu, hQv]
      omega
    have hcongr := (color.even_length_iff_congr W).1 hEven
    have hcolorEq : color u = color v := by
      cases hu : color u <;> cases hv : color v
      · rfl
      · simp [hu, hv] at hcongr
      · simp [hu, hv] at hcongr
      · rfl
    exact (color.valid huv) hcolorEq
  have hpositive : 1 ≤ Nat.dist (G.dist w u) (G.dist w v) :=
    Nat.dist_pos_of_ne hlevelsNe
  omega

/-- In a disjoint pure-mass tiling, the two endpoint levels of the q3 block
contain no off-corridor vertex.  This is the endpoint fact used by the local
alignment theorem; it follows from interval disjointness, not from an extra
attachment assumption. -/
theorem IsGeodesic.q3PureMass_noOffVertex_at_blockEndpoints
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P)
    (Cstar : OffCorridorComponent P) (l : ℕ)
    (hstarSize : (offCorridorComponentFinset Cstar).card = 3)
    (hstarInterval : offCorridorComponentIntervalEdges P Cstar =
      Finset.Ico l (l + 4))
    (hothers : ∀ C : OffCorridorComponent P, C ≠ Cstar →
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2)
    (hdisjoint :
      (Set.univ : Set (OffCorridorComponent P)).PairwiseDisjoint
        (offCorridorComponentIntervalEdges P)) :
    ∀ z ∈ offCorridorFinset P,
      G.dist w z ≠ l ∧ G.dist w z ≠ l + 4 := by
  classical
  intro z hzOff
  have hzNot : z ∉ P.support := by
    have := (Finset.mem_sdiff.mp hzOff).2
    simpa [supportFinset] using this
  let C := offCorridorComponentOf P z hzNot
  have hzC : z ∈ offCorridorComponentFinset C :=
    mem_offCorridorComponentOf P hzNot
  by_cases hCstar : C = Cstar
  · have hzCstar : z ∈ offCorridorComponentFinset Cstar := by
      simpa [hCstar] using hzC
    have hzImage : G.dist w z ∈
        (offCorridorComponentFinset Cstar).image (G.dist w) :=
      Finset.mem_image.mpr ⟨z, hzCstar, rfl⟩
    rw [IsGeodesic.image_rootDist_triple_spanFour
      hconn hP Cstar l hstarSize hstarInterval] at hzImage
    have hzBounds := Finset.mem_Ioo.mp hzImage
    exact ⟨by omega, by omega⟩
  · obtain ⟨hsize, hspan⟩ := hothers C hCstar
    obtain ⟨a, hinterval⟩ :=
      offCorridorInterval_eq_Ico_of_card_eq_two P C hspan
    have hzImage : G.dist w z ∈
        (offCorridorComponentFinset C).image (G.dist w) :=
      Finset.mem_image.mpr ⟨z, hzC, rfl⟩
    rw [IsGeodesic.image_rootDist_singleton_spanTwo
      hconn hP C a hsize hinterval] at hzImage
    have hzBounds := Finset.mem_Ioo.mp hzImage
    have hzLevel : G.dist w z = a + 1 := by omega
    have hd := hdisjoint (by simp) (by simp) hCstar
    have hdMem := Finset.disjoint_left.mp hd
    constructor
    · intro hzEq
      have hmemC : l ∈ offCorridorComponentIntervalEdges P C := by
        rw [hinterval]
        exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
      have hmemStar : l ∈ offCorridorComponentIntervalEdges P Cstar := by
        rw [hstarInterval]
        exact Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
      exact hdMem hmemC hmemStar
    · intro hzEq
      have hmemC : l + 3 ∈ offCorridorComponentIntervalEdges P C := by
        rw [hinterval]
        exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
      have hmemStar : l + 3 ∈
          offCorridorComponentIntervalEdges P Cstar := by
        rw [hstarInterval]
        exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
      exact hdMem hmemC hmemStar

/-- Generic endpoint-exclusion principle for a disjoint interval family
whose component vertices occupy strict interval interiors. -/
theorem noOffVertex_at_componentIntervalEndpoints
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ : V} {P : G.Walk w x₀}
    (Cstar : OffCorridorComponent P) (l h : ℕ) (hpos : 1 ≤ h)
    (hstarInterval : offCorridorComponentIntervalEdges P Cstar =
      Finset.Ico l (l + h))
    (hstarImage : (offCorridorComponentFinset Cstar).image (G.dist w) =
      Finset.Ioo l (l + h))
    (hdisjoint :
      (Set.univ : Set (OffCorridorComponent P)).PairwiseDisjoint
        (offCorridorComponentIntervalEdges P))
    (hinterior : ∀ C : OffCorridorComponent P,
      ∃ a q : ℕ, 1 ≤ q ∧
        offCorridorComponentIntervalEdges P C = Finset.Ico a (a + q) ∧
        (offCorridorComponentFinset C).image (G.dist w) =
          Finset.Ioo a (a + q)) :
    ∀ z ∈ offCorridorFinset P,
      G.dist w z ≠ l ∧ G.dist w z ≠ l + h := by
  classical
  intro z hzOff
  have hzNot : z ∉ P.support := by
    have := (Finset.mem_sdiff.mp hzOff).2
    simpa [supportFinset] using this
  let C := offCorridorComponentOf P z hzNot
  have hzC : z ∈ offCorridorComponentFinset C :=
    mem_offCorridorComponentOf P hzNot
  by_cases hCstar : C = Cstar
  · have hzStar : z ∈ offCorridorComponentFinset Cstar := by
      simpa [hCstar] using hzC
    have hzImage : G.dist w z ∈
        (offCorridorComponentFinset Cstar).image (G.dist w) :=
      Finset.mem_image.mpr ⟨z, hzStar, rfl⟩
    rw [hstarImage] at hzImage
    have hzBounds := Finset.mem_Ioo.mp hzImage
    exact ⟨by omega, by omega⟩
  · obtain ⟨a, q, hq, hinterval, himage⟩ := hinterior C
    have hzImage : G.dist w z ∈
        (offCorridorComponentFinset C).image (G.dist w) :=
      Finset.mem_image.mpr ⟨z, hzC, rfl⟩
    rw [himage] at hzImage
    have hzBounds := Finset.mem_Ioo.mp hzImage
    have hd := hdisjoint (by simp) (by simp) hCstar
    have hdMem := Finset.disjoint_left.mp hd
    constructor
    · intro hzEq
      have hmemC : l ∈ offCorridorComponentIntervalEdges P C := by
        rw [hinterval]
        exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
      have hmemStar : l ∈ offCorridorComponentIntervalEdges P Cstar := by
        rw [hstarInterval]
        exact Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
      exact hdMem hmemC hmemStar
    · intro hzEq
      have hmemC : l + h - 1 ∈ offCorridorComponentIntervalEdges P C := by
        rw [hinterval]
        exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
      have hmemStar : l + h - 1 ∈
          offCorridorComponentIntervalEdges P Cstar := by
        rw [hstarInterval]
        exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
      exact hdMem hmemC hmemStar

/-- Both size-two blocks in the pure-mass `q2+q2` shape have empty
off-corridor endpoint levels. -/
theorem IsGeodesic.q2q2PureMass_noOffVertex_at_blockEndpoints
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (color : G.Coloring Bool) (hP : IsGeodesic P)
    (Ca Cb : OffCorridorComponent P) (la lb : ℕ)
    (hCaSize : (offCorridorComponentFinset Ca).card = 2)
    (hCbSize : (offCorridorComponentFinset Cb).card = 2)
    (hCaInterval : offCorridorComponentIntervalEdges P Ca =
      Finset.Ico la (la + 3))
    (hCbInterval : offCorridorComponentIntervalEdges P Cb =
      Finset.Ico lb (lb + 3))
    (hothers : ∀ C : OffCorridorComponent P, C ≠ Ca → C ≠ Cb →
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2)
    (hdisjoint :
      (Set.univ : Set (OffCorridorComponent P)).PairwiseDisjoint
        (offCorridorComponentIntervalEdges P)) :
    (∀ z ∈ offCorridorFinset P,
      G.dist w z ≠ la ∧ G.dist w z ≠ la + 3) ∧
    (∀ z ∈ offCorridorFinset P,
      G.dist w z ≠ lb ∧ G.dist w z ≠ lb + 3) := by
  classical
  have himageInterior : ∀ C : OffCorridorComponent P,
      ∃ a q : ℕ, 1 ≤ q ∧
        offCorridorComponentIntervalEdges P C = Finset.Ico a (a + q) ∧
        (offCorridorComponentFinset C).image (G.dist w) =
          Finset.Ioo a (a + q) := by
    intro C
    by_cases hCA : C = Ca
    · subst C
      exact ⟨la, 3, by omega, hCaInterval,
        IsGeodesic.image_rootDist_pair_spanThree
          hconn color hP Ca la hCaSize hCaInterval⟩
    · by_cases hCB : C = Cb
      · subst C
        exact ⟨lb, 3, by omega, hCbInterval,
          IsGeodesic.image_rootDist_pair_spanThree
            hconn color hP Cb lb hCbSize hCbInterval⟩
      · obtain ⟨hsize, hspan⟩ := hothers C hCA hCB
        obtain ⟨a, hinterval⟩ :=
          offCorridorInterval_eq_Ico_of_card_eq_two P C hspan
        exact ⟨a, 2, by omega, hinterval,
          IsGeodesic.image_rootDist_singleton_spanTwo
            hconn hP C a hsize hinterval⟩
  constructor
  · exact noOffVertex_at_componentIntervalEndpoints
      Ca la 3 (by omega) hCaInterval
      (IsGeodesic.image_rootDist_pair_spanThree
        hconn color hP Ca la hCaSize hCaInterval)
      hdisjoint himageInterior
  · exact noOffVertex_at_componentIntervalEndpoints
      Cb lb 3 (by omega) hCbInterval
      (IsGeodesic.image_rootDist_pair_spanThree
        hconn color hP Cb lb hCbSize hCbInterval)
      hdisjoint himageInterior

/-- A distance-four candidate of type A forbids its two length-two
shortcuts. -/
theorem IsGeodesic.q3_candidateA_chords_absent
    {V : Type*} {G : SimpleGraph V}
    {w x₀ x y cM cR : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P) {l : ℕ}
    (hlength : l + 4 ≤ P.length) (hMR : G.Adj cM cR)
    (hpair : PairMatches x y (P.getVert (l + 1)) cR)
    (hdist : G.dist x y = 4) :
    ¬G.Adj cM (P.getVert (l + 1)) ∧
      ¬G.Adj cR (P.getVert (l + 2)) := by
  have hcandidate : G.dist (P.getVert (l + 1)) cR = 4 := by
    rw [← dist_eq_of_pairMatches hpair]
    exact hdist
  constructor
  · intro hchord
    have h₁ : G.dist (P.getVert (l + 1)) cM = 1 :=
      dist_eq_one_iff_adj.mpr hchord.symm
    have h₂ : G.dist cM cR = 1 := dist_eq_one_iff_adj.mpr hMR
    have htri := hconn.dist_triangle
      (u := P.getVert (l + 1)) (v := cM) (w := cR)
    omega
  · intro hchord
    have hp : G.Adj (P.getVert (l + 1)) (P.getVert (l + 2)) :=
      P.adj_getVert_succ (i := l + 1) (by omega)
    have h₁ : G.dist (P.getVert (l + 1)) (P.getVert (l + 2)) = 1 :=
      dist_eq_one_iff_adj.mpr hp
    have h₂ : G.dist (P.getVert (l + 2)) cR = 1 :=
      dist_eq_one_iff_adj.mpr hchord.symm
    have htri := hconn.dist_triangle
      (u := P.getVert (l + 1)) (v := P.getVert (l + 2)) (w := cR)
    omega

/-- The central distance-four candidate forbids all four optional chords. -/
theorem IsGeodesic.q3_candidateB_chords_absent
    {V : Type*} {G : SimpleGraph V}
    {w x₀ x y cL cM cR : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P) {l : ℕ}
    (hlength : l + 4 ≤ P.length)
    (hLM : G.Adj cL cM) (hMR : G.Adj cM cR)
    (hpair : PairMatches x y (P.getVert (l + 2)) cM)
    (hdist : G.dist x y = 4) :
    ¬G.Adj cM (P.getVert (l + 1)) ∧
      ¬G.Adj cL (P.getVert (l + 2)) ∧
      ¬G.Adj cR (P.getVert (l + 2)) ∧
      ¬G.Adj cM (P.getVert (l + 3)) := by
  have hcandidate : G.dist (P.getVert (l + 2)) cM = 4 := by
    rw [← dist_eq_of_pairMatches hpair]
    exact hdist
  have hnoM1 : ¬G.Adj cM (P.getVert (l + 1)) := by
    intro hchord
    have hp : G.Adj (P.getVert (l + 1)) (P.getVert (l + 2)) :=
      P.adj_getVert_succ (i := l + 1) (by omega)
    have h₁ : G.dist (P.getVert (l + 2)) (P.getVert (l + 1)) = 1 :=
      dist_eq_one_iff_adj.mpr hp.symm
    have h₂ : G.dist (P.getVert (l + 1)) cM = 1 :=
      dist_eq_one_iff_adj.mpr hchord.symm
    have htri := hconn.dist_triangle
      (u := P.getVert (l + 2)) (v := P.getVert (l + 1)) (w := cM)
    omega
  have hnoL2 : ¬G.Adj cL (P.getVert (l + 2)) := by
    intro hchord
    have h₁ : G.dist (P.getVert (l + 2)) cL = 1 :=
      dist_eq_one_iff_adj.mpr hchord.symm
    have h₂ : G.dist cL cM = 1 := dist_eq_one_iff_adj.mpr hLM
    have htri := hconn.dist_triangle
      (u := P.getVert (l + 2)) (v := cL) (w := cM)
    omega
  have hnoR2 : ¬G.Adj cR (P.getVert (l + 2)) := by
    intro hchord
    have h₁ : G.dist (P.getVert (l + 2)) cR = 1 :=
      dist_eq_one_iff_adj.mpr hchord.symm
    have h₂ : G.dist cR cM = 1 := dist_eq_one_iff_adj.mpr hMR.symm
    have htri := hconn.dist_triangle
      (u := P.getVert (l + 2)) (v := cR) (w := cM)
    omega
  have hnoM3 : ¬G.Adj cM (P.getVert (l + 3)) := by
    intro hchord
    have hp : G.Adj (P.getVert (l + 2)) (P.getVert (l + 3)) :=
      P.adj_getVert_succ (i := l + 2) (by omega)
    have h₁ : G.dist (P.getVert (l + 2)) (P.getVert (l + 3)) = 1 :=
      dist_eq_one_iff_adj.mpr hp
    have h₂ : G.dist (P.getVert (l + 3)) cM = 1 :=
      dist_eq_one_iff_adj.mpr hchord.symm
    have htri := hconn.dist_triangle
      (u := P.getVert (l + 2)) (v := P.getVert (l + 3)) (w := cM)
    omega
  exact ⟨hnoM1, hnoL2, hnoR2, hnoM3⟩

/-- A distance-four candidate of type C forbids its two length-two
shortcuts. -/
theorem IsGeodesic.q3_candidateC_chords_absent
    {V : Type*} {G : SimpleGraph V}
    {w x₀ x y cL cM : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P) {l : ℕ}
    (hlength : l + 4 ≤ P.length) (hLM : G.Adj cL cM)
    (hpair : PairMatches x y (P.getVert (l + 3)) cL)
    (hdist : G.dist x y = 4) :
    ¬G.Adj cL (P.getVert (l + 2)) ∧
      ¬G.Adj cM (P.getVert (l + 3)) := by
  have hcandidate : G.dist (P.getVert (l + 3)) cL = 4 := by
    rw [← dist_eq_of_pairMatches hpair]
    exact hdist
  constructor
  · intro hchord
    have hp : G.Adj (P.getVert (l + 2)) (P.getVert (l + 3)) :=
      P.adj_getVert_succ (i := l + 2) (by omega)
    have h₁ : G.dist (P.getVert (l + 3)) (P.getVert (l + 2)) = 1 :=
      dist_eq_one_iff_adj.mpr hp.symm
    have h₂ : G.dist (P.getVert (l + 2)) cL = 1 :=
      dist_eq_one_iff_adj.mpr hchord.symm
    have htri := hconn.dist_triangle
      (u := P.getVert (l + 3)) (v := P.getVert (l + 2)) (w := cL)
    omega
  · intro hchord
    have h₁ : G.dist (P.getVert (l + 3)) cM = 1 :=
      dist_eq_one_iff_adj.mpr hchord.symm
    have h₂ : G.dist cM cL = 1 := dist_eq_one_iff_adj.mpr hLM.symm
    have htri := hconn.dist_triangle
      (u := P.getVert (l + 3)) (v := cM) (w := cL)
    omega

/-- With all four optional q3-to-corridor chords absent, the boundary after
`p_l` has exactly the corridor edge and the far q3 attachment as its possible
oriented crossing edges. -/
theorem IsGeodesic.q3_chordless_crossing_classifier
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ cL cM cR : V} {P : G.Walk w x₀}
    (hP : IsGeodesic P) (l : ℕ) (Cstar : OffCorridorComponent P)
    (hlength : l + 4 ≤ P.length)
    (hstar : offCorridorComponentFinset Cstar = {cL, cM, cR})
    (hstarInterval : offCorridorComponentIntervalEdges P Cstar =
      Finset.Ico l (l + 4))
    (hdisjoint :
      (Set.univ : Set (OffCorridorComponent P)).PairwiseDisjoint
        (offCorridorComponentIntervalEdges P))
    (hlevelL : G.dist w cL = l + 1)
    (hlevelM : G.dist w cM = l + 2)
    (hlevelR : G.dist w cR = l + 3)
    (hstep : ∀ {u v : V}, G.Adj u v →
      Nat.dist (G.dist w u) (G.dist w v) = 1)
    (hnoM1 : ¬G.Adj cM (P.getVert (l + 1)))
    (hnoL2 : ¬G.Adj cL (P.getVert (l + 2)))
    (hnoR2 : ¬G.Adj cR (P.getVert (l + 2)))
    (hnoM3 : ¬G.Adj cM (P.getVert (l + 3))) :
    ∀ {a b : V},
      a ∈ corridorLeftRegion P l → b ∉ corridorLeftRegion P l →
      G.Adj a b →
      (a = P.getVert l ∧ b = P.getVert (l + 1)) ∨
        (a = cR ∧ b = P.getVert (l + 4)) := by
  classical
  intro a b ha hb hab
  by_cases haP : a ∈ P.support
  · have hai : P.support.idxOf a ≤ l :=
      (mem_corridorLeftRegion_of_mem_support P l haP).1 ha
    by_cases hbP : b ∈ P.support
    · have hib : l < P.support.idxOf b := by
        by_contra hnot
        exact hb ((mem_corridorLeftRegion_of_mem_support P l hbP).2 (by omega))
      have hdist : Nat.dist (P.support.idxOf a) (P.support.idxOf b) = 1 := by
        rw [← hP.dist_eq_natDist_support_idxOf haP hbP]
        exact dist_eq_one_iff_adj.mpr hab
      have hsucc : P.support.idxOf b = P.support.idxOf a + 1 := by
        unfold Nat.dist at hdist
        omega
      have haidx : P.support.idxOf a = l := by omega
      have hbidx : P.support.idxOf b = l + 1 := by omega
      left
      exact ⟨by
        calc
          a = P.getVert (P.support.idxOf a) :=
            (P.getVert_support_idxOf haP).symm
          _ = P.getVert l := by rw [haidx], by
        calc
          b = P.getVert (P.support.idxOf b) :=
            (P.getVert_support_idxOf hbP).symm
          _ = P.getVert (l + 1) := by rw [hbidx]⟩
    · have haGet : P.getVert (P.support.idxOf a) = a :=
        P.getVert_support_idxOf haP
      have haIdxLe : P.support.idxOf a ≤ P.length :=
        support_idxOf_le_length P haP
      have hatt : P.support.idxOf a ∈
          offCorridorAttachmentIndices P (offCorridorComponentOf P b hbP) := by
        apply attachment_mem_of_offCorridor_adj P hbP haIdxLe
        simpa [haGet] using hab.symm
      have hbLeft : b ∈ corridorLeftRegion P l :=
        (mem_corridorLeftRegion_of_not_mem_support P l hbP).2
          ⟨P.support.idxOf a, hatt, hai⟩
      exact (hb hbLeft).elim
  · obtain ⟨j, hjatt, hji⟩ :=
      (mem_corridorLeftRegion_of_not_mem_support P l haP).1 ha
    by_cases hbP : b ∈ P.support
    · have hib : l < P.support.idxOf b := by
        by_contra hnot
        exact hb ((mem_corridorLeftRegion_of_mem_support P l hbP).2 (by omega))
      have hbIdxLe : P.support.idxOf b ≤ P.length :=
        support_idxOf_le_length P hbP
      have hbGet : P.getVert (P.support.idxOf b) = b :=
        P.getVert_support_idxOf hbP
      let Ca := offCorridorComponentOf P a haP
      have hbatt : P.support.idxOf b ∈ offCorridorAttachmentIndices P Ca := by
        apply attachment_mem_of_offCorridor_adj P haP hbIdxLe
        simpa [hbGet] using hab
      have hcover : offCorridorComponentCoversIndex P Ca l :=
        ⟨j, by simpa [Ca] using hjatt,
          P.support.idxOf b, hbatt, hji, by omega⟩
      have hiCa : l ∈ offCorridorComponentIntervalEdges P Ca :=
        mem_offCorridorComponentIntervalEdges_of_coversIndex P Ca hcover
      have hiStar : l ∈ offCorridorComponentIntervalEdges P Cstar := by
        rw [hstarInterval]
        exact Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
      have hCaStar : Ca = Cstar := by
        by_contra hne
        have hd := hdisjoint (by simp) (by simp) hne
        exact (Finset.disjoint_left.mp hd hiCa hiStar).elim
      have haOwn : a ∈ offCorridorComponentFinset Ca := by
        simpa [Ca] using mem_offCorridorComponentOf P haP
      have haStar : a ∈ offCorridorComponentFinset Cstar := by
        simpa [hCaStar] using haOwn
      have haCases : a = cL ∨ a = cM ∨ a = cR := by
        simpa [hstar] using haStar
      have hlevelB : G.dist w b = P.support.idxOf b := by
        calc
          G.dist w b = G.dist w (P.getVert (P.support.idxOf b)) :=
            congrArg (G.dist w) hbGet.symm
          _ = P.support.idxOf b :=
            IsGeodesic.rootDist_getVert hP hbIdxLe
      rcases haCases with haL | haM | haR
      · subst a
        have hcoord : P.support.idxOf b = l + 2 := by
          have hs := hstep hab
          rw [hlevelL, hlevelB] at hs
          unfold Nat.dist at hs
          omega
        exfalso
        apply hnoL2
        rw [← hbGet, hcoord] at hab
        exact hab
      · subst a
        have hcoord : P.support.idxOf b = l + 1 ∨
            P.support.idxOf b = l + 3 := by
          have hs := hstep hab
          rw [hlevelM, hlevelB] at hs
          unfold Nat.dist at hs
          omega
        rcases hcoord with hcoord | hcoord
        · exfalso
          apply hnoM1
          rw [← hbGet, hcoord] at hab
          exact hab
        · exfalso
          apply hnoM3
          rw [← hbGet, hcoord] at hab
          exact hab
      · subst a
        have hcoord : P.support.idxOf b = l + 2 ∨
            P.support.idxOf b = l + 4 := by
          have hs := hstep hab
          rw [hlevelR, hlevelB] at hs
          unfold Nat.dist at hs
          omega
        rcases hcoord with hcoord | hcoord
        · exfalso
          apply hnoR2
          rw [← hbGet, hcoord] at hab
          exact hab
        · right
          refine ⟨rfl, ?_⟩
          calc
            b = P.getVert (P.support.idxOf b) := hbGet.symm
            _ = P.getVert (l + 4) := by rw [hcoord]
    · have hcomp := offCorridorComponentOf_eq_of_adj P haP hbP hab
      have hbLeft : b ∈ corridorLeftRegion P l :=
        (mem_corridorLeftRegion_of_not_mem_support P l hbP).2
          ⟨j, by simpa [hcomp] using hjatt, hji⟩
      exact (hb hbLeft).elim

/-- The finite left region at the first q3 boundary. -/
noncomputable def q3LeftCut
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ : V} (P : G.Walk w x₀) (l : ℕ) : Finset V := by
  classical
  exact (corridorLeftRegion P l).toFinset

/-- The chordless q3 boundary cut has capacity at most two. -/
theorem IsGeodesic.cutSize_q3LeftCut_le_two
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ cL cM cR : V} {P : G.Walk w x₀}
    (hP : IsGeodesic P) (l : ℕ) (Cstar : OffCorridorComponent P)
    (hlength : l + 4 ≤ P.length)
    (hstar : offCorridorComponentFinset Cstar = {cL, cM, cR})
    (hstarInterval : offCorridorComponentIntervalEdges P Cstar =
      Finset.Ico l (l + 4))
    (hdisjoint :
      (Set.univ : Set (OffCorridorComponent P)).PairwiseDisjoint
        (offCorridorComponentIntervalEdges P))
    (hlevelL : G.dist w cL = l + 1)
    (hlevelM : G.dist w cM = l + 2)
    (hlevelR : G.dist w cR = l + 3)
    (hstep : ∀ {u v : V}, G.Adj u v →
      Nat.dist (G.dist w u) (G.dist w v) = 1)
    (hnoM1 : ¬G.Adj cM (P.getVert (l + 1)))
    (hnoL2 : ¬G.Adj cL (P.getVert (l + 2)))
    (hnoR2 : ¬G.Adj cR (P.getVert (l + 2)))
    (hnoM3 : ¬G.Adj cM (P.getVert (l + 3))) :
    cutSize G (q3LeftCut P l) ≤ 2 := by
  classical
  let T := q3LeftCut P l
  let crossingPairs := T.sigma fun a => G.neighborFinset a \ T
  let allowed : Finset (Sigma fun _ : V => V) :=
    {⟨P.getVert l, P.getVert (l + 1)⟩,
      ⟨cR, P.getVert (l + 4)⟩}
  have hsubset : crossingPairs ⊆ allowed := by
    intro e he
    obtain ⟨a, b⟩ := e
    have heData : a ∈ T ∧ b ∈ G.neighborFinset a \ T := by
      simpa [crossingPairs] using he
    have haLeft : a ∈ corridorLeftRegion P l := by
      simpa [T, q3LeftCut] using heData.1
    have hbData : G.Adj a b ∧ b ∉ T := by simpa using heData.2
    have hbRight : b ∉ corridorLeftRegion P l := by
      simpa [T, q3LeftCut] using hbData.2
    rcases IsGeodesic.q3_chordless_crossing_classifier
      hP l Cstar hlength hstar hstarInterval hdisjoint
      hlevelL hlevelM hlevelR hstep hnoM1 hnoL2 hnoR2 hnoM3
      haLeft hbRight hbData.1 with hpath | hoff
    · simp [allowed, hpath.1, hpath.2]
    · simp [allowed, hoff.1, hoff.2]
  calc
    cutSize G (q3LeftCut P l) = crossingPairs.card := by
      simp [cutSize, crossingPairs, T, Finset.card_sigma]
    _ ≤ allowed.card := Finset.card_le_card hsubset
    _ ≤ 2 := Finset.card_le_two

/-- On the actual simple-demand surface, the q3 candidate set contains at
most one indexed demand.  Equal candidate types coincide as unordered pairs
and are identified by `hpairInjective`; two distinct types jointly forbid all
four optional chords, after which the residual-unit q3 cut and RFC give the
contradiction. -/
theorem q3_exception_card_le_one
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ cL cM cR : V} {P : G.Walk w x₀}
    (m₁ m₂ : I → V) (exceptional : I → Prop) [DecidablePred exceptional]
    (hconn : G.Connected) (hP : IsGeodesic P)
    (l : ℕ) (Cstar : OffCorridorComponent P)
    (hlength : l + 4 ≤ P.length)
    (hstar : offCorridorComponentFinset Cstar = {cL, cM, cR})
    (hstarInterval : offCorridorComponentIntervalEdges P Cstar =
      Finset.Ico l (l + 4))
    (hdisjoint :
      (Set.univ : Set (OffCorridorComponent P)).PairwiseDisjoint
        (offCorridorComponentIntervalEdges P))
    (hLM : G.Adj cL cM) (hMR : G.Adj cM cR)
    (hlevelL : G.dist w cL = l + 1)
    (hlevelM : G.dist w cM = l + 2)
    (hlevelR : G.dist w cR = l + 3)
    (hstep : ∀ {u v : V}, G.Adj u v →
      Nat.dist (G.dist w u) (G.dist w v) = 1)
    (hRFC : ∀ T : Finset V, w ∉ T →
      (∑ i : I, separationDemand T (m₁ i) (m₂ i)) +
        (if x₀ ∈ T then 1 else 0) ≤ cutSize G T)
    (hpairInjective : Function.Injective (fun i => s(m₁ i, m₂ i)))
    (hcandidate : ∀ i, exceptional i →
      G.dist (m₁ i) (m₂ i) = 4 ∧
        Q3ExceptionalPair P l cL cM cR (m₁ i) (m₂ i)) :
    ((Finset.univ : Finset I).filter exceptional).card ≤ 1 := by
  classical
  obtain ⟨hattL, _hattR, _hattBounds⟩ :=
    attachment_extrema_of_interval_eq_length P Cstar l 4 (by omega)
      hstarInterval
  have hcLstar : cL ∈ offCorridorComponentFinset Cstar := by simp [hstar]
  have hcMstar : cM ∈ offCorridorComponentFinset Cstar := by simp [hstar]
  have hcRstar : cR ∈ offCorridorComponentFinset Cstar := by simp [hstar]
  have hcLLeft : cL ∈ corridorLeftRegion P l :=
    mem_corridorLeftRegion_of_mem_offCorridorComponent
      Cstar hcLstar hattL le_rfl
  have hcMLeft : cM ∈ corridorLeftRegion P l :=
    mem_corridorLeftRegion_of_mem_offCorridorComponent
      Cstar hcMstar hattL le_rfl
  have hcRLeft : cR ∈ corridorLeftRegion P l :=
    mem_corridorLeftRegion_of_mem_offCorridorComponent
      Cstar hcRstar hattL le_rfl
  have hp1Right : P.getVert (l + 1) ∉ corridorLeftRegion P l :=
    hP.getVert_not_mem_corridorLeftRegion (by omega) (by omega)
  have hp2Right : P.getVert (l + 2) ∉ corridorLeftRegion P l :=
    hP.getVert_not_mem_corridorLeftRegion (by omega) (by omega)
  have hp3Right : P.getVert (l + 3) ∉ corridorLeftRegion P l :=
    hP.getVert_not_mem_corridorLeftRegion (by omega) (by omega)
  let T := Finset.univ \ q3LeftCut P l
  have hwLeft : w ∈ corridorLeftRegion P l := by
    simpa using hP.getVert_mem_corridorLeftRegion (j := 0) (by omega) (by omega)
  have hxRight : x₀ ∉ corridorLeftRegion P l := by
    simpa using hP.getVert_not_mem_corridorLeftRegion
      (j := P.length) le_rfl (by omega)
  have hroot : w ∉ T := by
    simp [T, q3LeftCut, hwLeft]
  have hstub : x₀ ∈ T := by
    simp [T, q3LeftCut, hxRight]
  have hp1T : P.getVert (l + 1) ∈ T := by
    simp [T, q3LeftCut, hp1Right]
  have hp2T : P.getVert (l + 2) ∈ T := by
    simp [T, q3LeftCut, hp2Right]
  have hp3T : P.getVert (l + 3) ∈ T := by
    simp [T, q3LeftCut, hp3Right]
  have hcLnotT : cL ∉ T := by simp [T, q3LeftCut, hcLLeft]
  have hcMnotT : cM ∉ T := by simp [T, q3LeftCut, hcMLeft]
  have hcRnotT : cR ∉ T := by simp [T, q3LeftCut, hcRLeft]
  have hsupported : ∀ i, exceptional i → Separates T (m₁ i) (m₂ i) := by
    intro i hi
    rcases (hcandidate i hi).2 with hA | hB | hC
    · rcases hA with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [h₁, h₂]
        exact Or.inl ⟨hp1T, hcRnotT⟩
      · rw [h₁, h₂]
        exact Or.inr ⟨hcRnotT, hp1T⟩
    · rcases hB with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [h₁, h₂]
        exact Or.inl ⟨hp2T, hcMnotT⟩
      · rw [h₁, h₂]
        exact Or.inr ⟨hcMnotT, hp2T⟩
    · rcases hC with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [h₁, h₂]
        exact Or.inl ⟨hp3T, hcLnotT⟩
      · rw [h₁, h₂]
        exact Or.inr ⟨hcLnotT, hp3T⟩
  rw [Finset.card_le_one]
  intro i hi j hj
  have hiExceptional : exceptional i := (Finset.mem_filter.mp hi).2
  have hjExceptional : exceptional j := (Finset.mem_filter.mp hj).2
  obtain ⟨hiDist, hiCand⟩ := hcandidate i hiExceptional
  obtain ⟨hjDist, hjCand⟩ := hcandidate j hjExceptional
  have viaCut (hchordless :
      ¬G.Adj cM (P.getVert (l + 1)) ∧
        ¬G.Adj cL (P.getVert (l + 2)) ∧
        ¬G.Adj cR (P.getVert (l + 2)) ∧
        ¬G.Adj cM (P.getVert (l + 3))) : i = j := by
    have hcutLeft := IsGeodesic.cutSize_q3LeftCut_le_two
      hP l Cstar hlength hstar hstarInterval hdisjoint
      hlevelL hlevelM hlevelR hstep
      hchordless.1 hchordless.2.1 hchordless.2.2.1 hchordless.2.2.2
    have hcut : cutSize G T ≤ 2 := by
      rw [show T = Finset.univ \ q3LeftCut P l by rfl,
        cutSize_univ_sdiff]
      exact hcutLeft
    have hresidual : cutSize G T ≤ (if x₀ ∈ T then 1 else 0) + 1 := by
      simp [hstub]
      exact hcut
    have hcard := rootedCutCondition_atMostOne_cutSupported_exception
      m₁ m₂ w x₀ hRFC T exceptional hroot hresidual hsupported
    exact (Finset.card_le_one.mp hcard) i hi j hj
  rcases hiCand with hiA | hiB | hiC
  · rcases hjCand with hjA | hjB | hjC
    · exact hpairInjective
        ((sym2_eq_of_pairMatches hiA).trans
          (sym2_eq_of_pairMatches hjA).symm)
    · exact viaCut (IsGeodesic.q3_candidateB_chords_absent
        hconn hP hlength hLM hMR hjB hjDist)
    · have hAabs := IsGeodesic.q3_candidateA_chords_absent
        hconn hP hlength hMR hiA hiDist
      have hCabs := IsGeodesic.q3_candidateC_chords_absent
        hconn hP hlength hLM hjC hjDist
      exact viaCut ⟨hAabs.1, hCabs.1, hAabs.2, hCabs.2⟩
  · rcases hjCand with hjA | hjB | hjC
    · exact viaCut (IsGeodesic.q3_candidateB_chords_absent
        hconn hP hlength hLM hMR hiB hiDist)
    · exact hpairInjective
        ((sym2_eq_of_pairMatches hiB).trans
          (sym2_eq_of_pairMatches hjB).symm)
    · exact viaCut (IsGeodesic.q3_candidateB_chords_absent
        hconn hP hlength hLM hMR hiB hiDist)
  · rcases hjCand with hjA | hjB | hjC
    · have hAabs := IsGeodesic.q3_candidateA_chords_absent
        hconn hP hlength hMR hjA hjDist
      have hCabs := IsGeodesic.q3_candidateC_chords_absent
        hconn hP hlength hLM hiC hiDist
      exact viaCut ⟨hAabs.1, hCabs.1, hAabs.2, hCabs.2⟩
    · exact viaCut (IsGeodesic.q3_candidateB_chords_absent
        hconn hP hlength hLM hMR hjB hjDist)
    · exact hpairInjective
        ((sym2_eq_of_pairMatches hiC).trans
          (sym2_eq_of_pairMatches hjC).symm)

/-- Complete graph-level closure of the pure-mass q3 branch at
`d = 2s-2`.  The hypotheses name only the canonical q3 component inside the
already-verified `PureMassShape`; all BFS geometry, the two-high capacity
profile, exceptional-pair classification, and RFC uniqueness are derived
here. -/
theorem totalCost_le_rlBudget_of_q3PureMass_allNonbridge_sameSide
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    [Fintype (OffCorridorComponent P)]
    (m₁ m₂ : I → V) (hconn : G.Connected) (color : G.Coloring Bool)
    (hP : IsGeodesic P)
    (htwo : P.length = 2 * slack P - 2)
    (hnonbridge : ∀ i < P.length,
      ¬G.IsBridge s(P.getVert i, P.getVert (i + 1)))
    (hpure :
      let components := (Finset.univ : Finset (OffCorridorComponent P))
      let size : OffCorridorComponent P → ℕ := fun C =>
        (offCorridorComponentFinset C).card
      let span : OffCorridorComponent P → ℕ := fun C =>
        (offCorridorComponentIntervalEdges P C).card
      let unionCard :=
        (components.biUnion (offCorridorComponentIntervalEdges P)).card
      PureMassShape components size span (slack P) unionCard)
    (Cstar : OffCorridorComponent P)
    (hstarSize : (offCorridorComponentFinset Cstar).card = 3)
    (hstarSpan : (offCorridorComponentIntervalEdges P Cstar).card = 4)
    (hothers : ∀ C : OffCorridorComponent P, C ≠ Cstar →
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2)
    (hRFC : ∀ T : Finset V, w ∉ T →
      (∑ i : I, separationDemand T (m₁ i) (m₂ i)) +
        (if x₀ ∈ T then 1 else 0) ≤ cutSize G T)
    (hpairInjective : Function.Injective (fun i => s(m₁ i, m₂ i)))
    (hs : 5 ≤ slack P)
    (hlegal : ∀ i, 4 ≤ G.dist (m₁ i) (m₂ i))
    (hsame : ∀ i, color (m₁ i) = color (m₂ i)) :
    (∑ i : I, (G.dist (m₁ i) (m₂ i) + 1) ^ 2) ≤
      rlBudget (slack P) (2 * slack P - 2) := by
  classical
  let components : Finset (OffCorridorComponent P) := Finset.univ
  let size : OffCorridorComponent P → ℕ := fun C =>
    (offCorridorComponentFinset C).card
  let interval : OffCorridorComponent P → Finset ℕ :=
    offCorridorComponentIntervalEdges P
  let span : OffCorridorComponent P → ℕ := fun C => (interval C).card
  let unionCard := (components.biUnion interval).card
  have hpureData := hpure
  change PureMassShape components size span (slack P) unionCard at hpureData
  have hoverlapZero : overlapDefect components span unionCard = 0 :=
    hpureData.2.2.1
  have hdisjointFin :
      (components : Set (OffCorridorComponent P)).PairwiseDisjoint interval := by
    apply pairwiseDisjoint_of_overlapDefect_eq_zero components interval
    exact hoverlapZero
  have hdisjoint :
      (Set.univ : Set (OffCorridorComponent P)).PairwiseDisjoint
        (offCorridorComponentIntervalEdges P) := by
    simpa [components, interval] using hdisjointFin
  obtain ⟨l, hstarIntervalRaw⟩ :=
    offCorridorInterval_eq_Ico_card P Cstar (by omega)
  have hstarInterval : offCorridorComponentIntervalEdges P Cstar =
      Finset.Ico l (l + 4) := by
    simpa [hstarSpan] using hstarIntervalRaw
  obtain ⟨_hattL, hattR, _hattBounds⟩ :=
    attachment_extrema_of_interval_eq_length P Cstar l 4 (by omega)
      hstarInterval
  have hlength : l + 4 ≤ P.length :=
    ((mem_offCorridorAttachmentIndices P Cstar (l + 4)).1 hattR).1
  obtain ⟨cL, cM, cR, hstar, _hcLM, _hcMR, _hcLR,
      hLM, hMR, hleft, hright, hlevelL, hlevelM, hlevelR⟩ :=
    IsGeodesic.triple_spanFour_geometry
      hconn hP Cstar l hstarSize hstarInterval
  have hcLstar : cL ∈ offCorridorComponentFinset Cstar := by simp [hstar]
  have hcMstar : cM ∈ offCorridorComponentFinset Cstar := by simp [hstar]
  have hcRstar : cR ∈ offCorridorComponentFinset Cstar := by simp [hstar]
  have hcLoff := mem_offCorridorFinset_of_mem_componentFinset hcLstar
  have hcMoff := mem_offCorridorFinset_of_mem_componentFinset hcMstar
  have hcRoff := mem_offCorridorFinset_of_mem_componentFinset hcRstar
  obtain ⟨levels, high, hlevelsCard, hactive, hhighEq, hhighCard,
      hlevelsSub, himage, hinjective⟩ :=
    IsGeodesic.pureMassTwoDefect_rootLevelProfile
      hconn color hP (by omega) htwo hnonbridge hpure
  have hnoEndpoint : ∀ z ∈ offCorridorFinset P,
      G.dist w z ≠ l ∧ G.dist w z ≠ l + 4 :=
    IsGeodesic.q3PureMass_noOffVertex_at_blockEndpoints
      hconn hP Cstar l hstarSize hstarInterval hothers hdisjoint
  have hvertexBound : ∀ v : V, G.dist w v ≤ P.length := by
    intro v
    by_cases hvSupport : v ∈ P.support
    · have hidx : P.support.idxOf v ≤ P.length :=
        support_idxOf_le_length P hvSupport
      have hget := P.getVert_support_idxOf hvSupport
      have hlevel := IsGeodesic.rootDist_getVert hP hidx
      rw [hget] at hlevel
      omega
    · have hvOff : v ∈ offCorridorFinset P :=
        Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ v, by simpa [supportFinset] using hvSupport⟩
      have hvImage : G.dist w v ∈
          (offCorridorFinset P).image (G.dist w) :=
        Finset.mem_image.mpr ⟨v, hvOff, rfl⟩
      rw [himage] at hvImage
      exact (Finset.mem_range.mp (hlevelsSub hvImage)).le
  have hstep : ∀ {u v : V}, G.Adj u v →
      Nat.dist (G.dist w u) (G.dist w v) = 1 := by
    intro u v huv
    have hupper := bfsLevel_natDist_le hconn w u v
    have hdistOne : G.dist u v = 1 := dist_eq_one_iff_adj.mpr huv
    have hlevelsNe : G.dist w u ≠ G.dist w v := by
      intro heq
      obtain ⟨Qu, hQu⟩ := hconn.exists_walk_length_eq_dist w u
      obtain ⟨Qv, hQv⟩ := hconn.exists_walk_length_eq_dist w v
      let W := Qu.reverse.append Qv
      have hEven : Even W.length := by
        refine ⟨G.dist w u, ?_⟩
        simp only [W, Walk.length_append, Walk.length_reverse, hQu, hQv]
        omega
      have hcongr := (color.even_length_iff_congr W).1 hEven
      have hcolorEq : color u = color v := by
        cases hu : color u <;> cases hv : color v
        · rfl
        · simp [hu, hv] at hcongr
        · simp [hu, hv] at hcongr
        · rfl
      exact (color.valid huv) hcolorEq
    have hpositive : 1 ≤ Nat.dist (G.dist w u) (G.dist w v) :=
      Nat.dist_pos_of_ne hlevelsNe
    omega
  have hrawClass : ∀ i,
      G.dist (m₁ i) (m₂ i) =
          Nat.dist (G.dist w (m₁ i)) (G.dist w (m₂ i)) ∨
        (G.dist (m₁ i) (m₂ i) = 4 ∧
          Q3ExceptionalPair P l cL cM cR (m₁ i) (m₂ i)) := by
    intro i
    exact IsGeodesic.q3PureMass_levelAligned_or_candidate
      hconn hP Cstar l hstar hothers hlength hLM hMR hleft hright
      hlevelL hlevelM hlevelR hcLoff hcMoff hcRoff hinjective
      hnoEndpoint (hvertexBound _) (hvertexBound _)
      (Coloring.even_natDist_rootLevels_of_eq hconn color w (hsame i))
      (hlegal i)
  have hp1Level := IsGeodesic.rootDist_getVert hP (k := l + 1) (by omega)
  have hp2Level := IsGeodesic.rootDist_getVert hP (k := l + 2) (by omega)
  have hp3Level := IsGeodesic.rootDist_getVert hP (k := l + 3) (by omega)
  have hclass : ∀ i,
      G.dist (m₁ i) (m₂ i) =
          Nat.dist (G.dist w (m₁ i)) (G.dist w (m₂ i)) ∨
        (G.dist (m₁ i) (m₂ i) = 4 ∧
          (Nat.dist (G.dist w (m₁ i)) (G.dist w (m₂ i)) = 0 ∨
            Nat.dist (G.dist w (m₁ i)) (G.dist w (m₂ i)) = 2)) := by
    intro i
    rcases hrawClass i with haligned | ⟨hdist, hA | hB | hC⟩
    · exact Or.inl haligned
    · right
      refine ⟨hdist, Or.inr ?_⟩
      rcases hA with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [h₁, h₂, hp1Level, hlevelR]
        simp [Nat.dist]
      · rw [h₁, h₂, hp1Level, hlevelR]
        simp [Nat.dist]
    · right
      refine ⟨hdist, Or.inl ?_⟩
      rcases hB with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [h₁, h₂, hp2Level, hlevelM]
        simp [Nat.dist]
      · rw [h₁, h₂, hp2Level, hlevelM]
        simp [Nat.dist]
    · right
      refine ⟨hdist, Or.inr ?_⟩
      rcases hC with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [h₁, h₂, hp3Level, hlevelL]
        simp [Nat.dist]
      · rw [h₁, h₂, hp3Level, hlevelL]
        simp [Nat.dist]
  let exceptional : I → Prop := fun i =>
    G.dist (m₁ i) (m₂ i) ≠
      Nat.dist (G.dist w (m₁ i)) (G.dist w (m₂ i))
  have hexceptionCount :
      ((Finset.univ : Finset I).filter exceptional).card ≤ 1 := by
    apply q3_exception_card_le_one m₁ m₂ exceptional
      hconn hP l Cstar hlength hstar hstarInterval hdisjoint
      hLM hMR hlevelL hlevelM hlevelR hstep hRFC hpairInjective
    intro i hi
    rcases hrawClass i with haligned | hexception
    · exact (hi haligned).elim
    · exact hexception
  let extra : ℕ → ℕ := fun k => if k ∈ levels then 1 else 0
  let capacity : Fin P.length → ℕ := fun r =>
    extra r.1 + extra (r.1 + 1) + extra r.1 * extra (r.1 + 1)
  let highFin : Finset (Fin P.length) :=
    (Finset.univ : Finset (Fin P.length)).filter fun r => r.1 ∈ high
  have hhighSub : high ⊆ Finset.range P.length := by
    intro k hk
    rw [hhighEq] at hk
    exact (Finset.mem_filter.mp hk).1
  have himageHigh : highFin.image Fin.val = high := by
    ext k
    constructor
    · intro hk
      obtain ⟨r, hr, hrk⟩ := Finset.mem_image.mp hk
      have hrHigh : r.1 ∈ high := by simpa [highFin] using hr
      simpa [← hrk] using hrHigh
    · intro hk
      let r : Fin P.length := ⟨k, Finset.mem_range.mp (hhighSub hk)⟩
      exact Finset.mem_image.mpr
        ⟨r, by simp [highFin, r, hk], rfl⟩
  have hhighFinCard : highFin.card ≤ 2 := by
    have hinj : Set.InjOn Fin.val (highFin : Set (Fin P.length)) :=
      fun _ _ _ _ h => Fin.ext h
    have hcardEq : (highFin.image Fin.val).card = highFin.card :=
      Finset.card_image_iff.mpr hinj
    rw [himageHigh] at hcardEq
    omega
  have hlayer : ∀ k ≤ P.length,
      (levelLayer (G.dist w) k).card = extra k + 1 := by
    intro k hk
    have h := IsGeodesic.levelLayer_card_eq_one_add_indicator
      hP levels hinjective himage hk
    simpa [extra, Nat.add_comm] using h
  have hcut : ∀ r : Fin P.length,
      cutSize G (levelUpperCut (G.dist w) r.1) ≤ capacity r + 1 := by
    intro r
    have hproduct := cutSize_levelUpperCut_le_layerProduct
      (G.dist w) hstep r.1
    rw [hlayer r.1 (by omega), hlayer (r.1 + 1) (by omega)] at hproduct
    dsimp [capacity]
    nlinarith
  have hcapacity : ∀ r, capacity r ≤ if r ∈ highFin then 3 else 1 := by
    intro r
    have hact := hactive r.1 r.2
    by_cases h0 : r.1 ∈ levels
    · by_cases h1 : r.1 + 1 ∈ levels
      · have hrHigh : r ∈ highFin := by
          simp [highFin, hhighEq, r.2, h0, h1]
        simp [capacity, extra, h0, h1, hrHigh]
      · have hrNot : r ∉ highFin := by
          simp [highFin, hhighEq, h1]
        simp [capacity, extra, h0, h1, hrNot]
    · by_cases h1 : r.1 + 1 ∈ levels
      · have hrNot : r ∉ highFin := by
          simp [highFin, hhighEq, h0]
        simp [capacity, extra, h0, h1, hrNot]
      · exfalso
        exact hact.elim h0 h1
  have hroot : G.dist w w = 0 := by simp
  have hstub : G.dist w x₀ = P.length := hP.symm
  have hresult := totalCost_le_rlBudget_of_q3_zeroOrOneExceptionLevelCuts
    w x₀ m₁ m₂ (G.dist w) (slack P) P.length capacity highFin
    hs htwo hroot hstub
    (fun i => hvertexBound (m₁ i)) (fun i => hvertexBound (m₂ i))
    hclass (by simpa [exceptional] using hexceptionCount)
    hRFC hcut hlegal hhighFinCard hcapacity
  simpa [htwo] using hresult

/-- Complete graph-level closure of the pure-mass `q2+q2` branch at
`d = 2s-2`. -/
theorem totalCost_le_rlBudget_of_q2q2PureMass_allNonbridge_sameSide
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    [Fintype (OffCorridorComponent P)]
    (m₁ m₂ : I → V) (hconn : G.Connected) (color : G.Coloring Bool)
    (hP : IsGeodesic P)
    (htwo : P.length = 2 * slack P - 2)
    (hnonbridge : ∀ i < P.length,
      ¬G.IsBridge s(P.getVert i, P.getVert (i + 1)))
    (hpure :
      let components := (Finset.univ : Finset (OffCorridorComponent P))
      let size : OffCorridorComponent P → ℕ := fun C =>
        (offCorridorComponentFinset C).card
      let span : OffCorridorComponent P → ℕ := fun C =>
        (offCorridorComponentIntervalEdges P C).card
      let unionCard :=
        (components.biUnion (offCorridorComponentIntervalEdges P)).card
      PureMassShape components size span (slack P) unionCard)
    (Ca Cb : OffCorridorComponent P) (hAB : Ca ≠ Cb)
    (hCaSize : (offCorridorComponentFinset Ca).card = 2)
    (hCaSpan : (offCorridorComponentIntervalEdges P Ca).card = 3)
    (hCbSize : (offCorridorComponentFinset Cb).card = 2)
    (hCbSpan : (offCorridorComponentIntervalEdges P Cb).card = 3)
    (hothers : ∀ C : OffCorridorComponent P, C ≠ Ca → C ≠ Cb →
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2)
    (hRFC : ∀ T : Finset V, w ∉ T →
      (∑ i : I, separationDemand T (m₁ i) (m₂ i)) +
        (if x₀ ∈ T then 1 else 0) ≤ cutSize G T)
    (hs : 5 ≤ slack P)
    (hlegal : ∀ i, 4 ≤ G.dist (m₁ i) (m₂ i))
    (hsame : ∀ i, color (m₁ i) = color (m₂ i)) :
    (∑ i : I, (G.dist (m₁ i) (m₂ i) + 1) ^ 2) ≤
      rlBudget (slack P) (2 * slack P - 2) := by
  classical
  let components : Finset (OffCorridorComponent P) := Finset.univ
  let size : OffCorridorComponent P → ℕ := fun C =>
    (offCorridorComponentFinset C).card
  let interval : OffCorridorComponent P → Finset ℕ :=
    offCorridorComponentIntervalEdges P
  let span : OffCorridorComponent P → ℕ := fun C => (interval C).card
  let unionCard := (components.biUnion interval).card
  have hpureData := hpure
  change PureMassShape components size span (slack P) unionCard at hpureData
  have hoverlapZero : overlapDefect components span unionCard = 0 :=
    hpureData.2.2.1
  have hdisjointFin :
      (components : Set (OffCorridorComponent P)).PairwiseDisjoint interval := by
    apply pairwiseDisjoint_of_overlapDefect_eq_zero components interval
    exact hoverlapZero
  have hdisjoint :
      (Set.univ : Set (OffCorridorComponent P)).PairwiseDisjoint
        (offCorridorComponentIntervalEdges P) := by
    simpa [components, interval] using hdisjointFin
  obtain ⟨la, hCaIntervalRaw⟩ :=
    offCorridorInterval_eq_Ico_card P Ca (by omega)
  obtain ⟨lb, hCbIntervalRaw⟩ :=
    offCorridorInterval_eq_Ico_card P Cb (by omega)
  have hCaInterval : offCorridorComponentIntervalEdges P Ca =
      Finset.Ico la (la + 3) := by simpa [hCaSpan] using hCaIntervalRaw
  have hCbInterval : offCorridorComponentIntervalEdges P Cb =
      Finset.Ico lb (lb + 3) := by simpa [hCbSpan] using hCbIntervalRaw
  obtain ⟨_hCaL, hCaR, _hCaBounds⟩ :=
    attachment_extrema_of_interval_eq_length P Ca la 3 (by omega) hCaInterval
  obtain ⟨_hCbL, hCbR, _hCbBounds⟩ :=
    attachment_extrema_of_interval_eq_length P Cb lb 3 (by omega) hCbInterval
  have hAlength : la + 3 ≤ P.length :=
    ((mem_offCorridorAttachmentIndices P Ca (la + 3)).1 hCaR).1
  have hBlength : lb + 3 ≤ P.length :=
    ((mem_offCorridorAttachmentIndices P Cb (lb + 3)).1 hCbR).1
  obtain ⟨aL, aR, hCaSet, _haNe, hALR, hAleft, hAright,
      hlevelAL, hlevelAR⟩ :=
    IsGeodesic.pair_spanThree_geometry
      hconn color hP Ca la hCaSize hCaInterval
  obtain ⟨bL, bR, hCbSet, _hbNe, hBLR, hBleft, hBright,
      hlevelBL, hlevelBR⟩ :=
    IsGeodesic.pair_spanThree_geometry
      hconn color hP Cb lb hCbSize hCbInterval
  have haLoff := mem_offCorridorFinset_of_mem_componentFinset
    (C := Ca) (by simp [hCaSet] : aL ∈ offCorridorComponentFinset Ca)
  have haRoff := mem_offCorridorFinset_of_mem_componentFinset
    (C := Ca) (by simp [hCaSet] : aR ∈ offCorridorComponentFinset Ca)
  have hbLoff := mem_offCorridorFinset_of_mem_componentFinset
    (C := Cb) (by simp [hCbSet] : bL ∈ offCorridorComponentFinset Cb)
  have hbRoff := mem_offCorridorFinset_of_mem_componentFinset
    (C := Cb) (by simp [hCbSet] : bR ∈ offCorridorComponentFinset Cb)
  obtain ⟨hnoAEndpoint, hnoBEndpoint⟩ :=
    IsGeodesic.q2q2PureMass_noOffVertex_at_blockEndpoints
      hconn color hP Ca Cb la lb hCaSize hCbSize
      hCaInterval hCbInterval hothers hdisjoint
  obtain ⟨levels, high, _hlevelsCard, hactive, hhighEq, hhighCard,
      hlevelsSub, himage, hinjective⟩ :=
    IsGeodesic.pureMassTwoDefect_rootLevelProfile
      hconn color hP (by omega) htwo hnonbridge hpure
  have hvertexBound : ∀ v : V, G.dist w v ≤ P.length := by
    intro v
    by_cases hvSupport : v ∈ P.support
    · have hidx : P.support.idxOf v ≤ P.length :=
        support_idxOf_le_length P hvSupport
      have hget := P.getVert_support_idxOf hvSupport
      have hlevel := IsGeodesic.rootDist_getVert hP hidx
      rw [hget] at hlevel
      omega
    · have hvOff : v ∈ offCorridorFinset P :=
        Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ v, by simpa [supportFinset] using hvSupport⟩
      have hvImage : G.dist w v ∈
          (offCorridorFinset P).image (G.dist w) :=
        Finset.mem_image.mpr ⟨v, hvOff, rfl⟩
      rw [himage] at hvImage
      exact (Finset.mem_range.mp (hlevelsSub hvImage)).le
  have hstep : ∀ {u v : V}, G.Adj u v →
      Nat.dist (G.dist w u) (G.dist w v) = 1 := by
    intro u v huv
    exact Coloring.adj_rootDist_natDist_eq_one hconn color huv
  have horderCases : la + 3 ≤ lb ∨ lb + 3 ≤ la := by
    by_cases horder : la + 3 ≤ lb
    · exact Or.inl horder
    · right
      by_contra hreverse
      have hABdisj := hdisjoint (by simp) (by simp) hAB
      let k := max la lb
      have hkA : k ∈ offCorridorComponentIntervalEdges P Ca := by
        rw [hCaInterval]
        exact Finset.mem_Ico.mpr ⟨le_max_left _ _, by
          dsimp [k]
          omega⟩
      have hkB : k ∈ offCorridorComponentIntervalEdges P Cb := by
        rw [hCbInterval]
        exact Finset.mem_Ico.mpr ⟨le_max_right _ _, by
          dsimp [k]
          omega⟩
      exact (Finset.disjoint_left.mp hABdisj hkA hkB).elim
  have haligned : ∀ i,
      G.dist (m₁ i) (m₂ i) =
        Nat.dist (G.dist w (m₁ i)) (G.dist w (m₂ i)) := by
    intro i
    rcases horderCases with horder | horder
    · exact IsGeodesic.q2q2PureMass_levelAligned
        hconn hP Ca Cb la lb hCaSet hCbSet hothers horder hBlength
        hALR hBLR hAleft hAright hBleft hBright
        hlevelAL hlevelAR hlevelBL hlevelBR
        haLoff haRoff hbLoff hbRoff hinjective hnoAEndpoint hnoBEndpoint
        (hvertexBound _) (hvertexBound _)
        (Coloring.even_natDist_rootLevels_of_eq hconn color w (hsame i))
        (hlegal i)
    · exact IsGeodesic.q2q2PureMass_levelAligned
        hconn hP Cb Ca lb la hCbSet hCaSet
        (fun C hCneB hCneA => hothers C hCneA hCneB)
        horder hAlength hBLR hALR hBleft hBright hAleft hAright
        hlevelBL hlevelBR hlevelAL hlevelAR
        hbLoff hbRoff haLoff haRoff hinjective hnoBEndpoint hnoAEndpoint
        (hvertexBound _) (hvertexBound _)
        (Coloring.even_natDist_rootLevels_of_eq hconn color w (hsame i))
        (hlegal i)
  have hresult := totalCost_le_rlBudget_of_aligned_twoHighRootLevelProfile
    m₁ m₂ levels high (slack P) P.length hs rfl htwo hP
    hactive hhighEq (by omega) hlevelsSub himage hinjective
    hvertexBound hstep haligned hRFC hlegal
  simpa [htwo] using hresult

/-- A zero-span singleton component is a genuine pendant vertex.  Its
unique neighbor is one corridor vertex, and its BFS level is one beyond that
attachment coordinate. -/
theorem IsGeodesic.singleton_spanZero_pendant_geometry
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P)
    (C : OffCorridorComponent P)
    (hsize : (offCorridorComponentFinset C).card = 1)
    (hspan : (offCorridorComponentIntervalEdges P C).card = 0) :
    ∃ z : V, ∃ a ≤ P.length,
      offCorridorComponentFinset C = {z} ∧
      G.dist w z = a + 1 ∧
      G.neighborFinset z = {P.getVert a} ∧
      cutSize G {z} = 1 := by
  classical
  obtain ⟨z, hset⟩ := Finset.card_eq_one.mp hsize
  have hzC : z ∈ offCorridorComponentFinset C := by simp [hset]
  have hzComp := (mem_offCorridorComponentFinset C).1 hzC
  obtain ⟨hzOffSet, hzCompEq⟩ := ComponentCompl.mem_supp_iff.mp hzComp
  have hzOff : z ∉ P.support := by simpa [supportFinset] using hzOffSet
  have hwSupport : w ∈ P.support := by
    simpa using P.getVert_mem_support 0
  have hzw : z ≠ w := by
    intro h
    subst z
    exact hzOff hwSupport
  letI : Nontrivial V := ⟨⟨z, w, hzw⟩⟩
  obtain ⟨y, hzy⟩ := hconn.preconnected.exists_adj_of_nontrivial z
  have hySupport : y ∈ P.support := by
    by_contra hyOff
    have hcompEq : offCorridorComponentOf P z hzOff =
        offCorridorComponentOf P y hyOff :=
      offCorridorComponentOf_eq_of_adj P hzOff hyOff hzy
    have hzOwn : offCorridorComponentOf P z hzOff = C := by
      simpa [offCorridorComponentOf, supportFinset] using hzCompEq
    have hyOwn : y ∈ offCorridorComponentFinset
        (offCorridorComponentOf P y hyOff) :=
      mem_offCorridorComponentOf P hyOff
    have hyC : y ∈ offCorridorComponentFinset C := by
      simpa [← hzOwn, hcompEq] using hyOwn
    have hyz : y = z := by simpa [hset] using hyC
    subst y
    exact G.loopless.irrefl z hzy
  let a := P.support.idxOf y
  have ha : a ≤ P.length := support_idxOf_le_length P hySupport
  have hget : P.getVert a = y := P.getVert_support_idxOf hySupport
  have haAttach : a ∈ offCorridorAttachmentIndices P C := by
    exact (mem_offCorridorAttachmentIndices P C a).2
      ⟨ha, z, hzC, by simpa [hget] using hzy⟩
  have hattachUnique : ∀ j ∈ offCorridorAttachmentIndices P C, j = a := by
    intro j hj
    by_contra hja
    have hlt : min a j < max a j := by
      rw [min_lt_max]
      exact fun haj => hja haj.symm
    have hgap : min a j ∈ Finset.Ico (min a j) (max a j) :=
      Finset.mem_Ico.mpr ⟨le_rfl, hlt⟩
    have hsubset := attachmentGapEdges_subset_componentInterval
      P C haAttach hj
    have hmem := hsubset hgap
    have hpos := Finset.card_pos.mpr
      ⟨min a j, hmem⟩
    omega
  have hneighborUnique : ∀ u : V, G.Adj z u → u = y := by
    intro u hzu
    by_cases huSupport : u ∈ P.support
    · let j := P.support.idxOf u
      have hj : j ≤ P.length := support_idxOf_le_length P huSupport
      have hju : P.getVert j = u := P.getVert_support_idxOf huSupport
      have hjAttach : j ∈ offCorridorAttachmentIndices P C := by
        exact (mem_offCorridorAttachmentIndices P C j).2
          ⟨hj, z, hzC, by simpa [hju] using hzu⟩
      have hja := hattachUnique j hjAttach
      calc
        u = P.getVert j := hju.symm
        _ = P.getVert a := by rw [hja]
        _ = y := hget
    · have hcompEq : offCorridorComponentOf P z hzOff =
          offCorridorComponentOf P u huSupport :=
        offCorridorComponentOf_eq_of_adj P hzOff huSupport hzu
      have hzOwn : offCorridorComponentOf P z hzOff = C := by
        simpa [offCorridorComponentOf, supportFinset] using hzCompEq
      have huOwn := mem_offCorridorComponentOf P huSupport
      have huC : u ∈ offCorridorComponentFinset C := by
        simpa [← hzOwn, hcompEq] using huOwn
      have huz : u = z := by simpa [hset] using huC
      subst u
      exact (G.loopless.irrefl z hzu).elim
  have hneighbors : G.neighborFinset z = {y} := by
    ext u
    constructor
    · intro hu
      have hzu : G.Adj z u := by simpa using hu
      simpa [hneighborUnique u hzu]
    · intro hu
      have huy : u = y := by simpa using hu
      subst u
      simpa using hzy
  have hlevelY : G.dist w y = a := by
    rw [← hget]
    exact IsGeodesic.rootDist_getVert hP ha
  have hlevelUpper : G.dist w z ≤ a + 1 := by
    have htri := hconn.dist_triangle (u := w) (v := y) (w := z)
    have hyzDist : G.dist y z = 1 := dist_eq_one_iff_adj.mpr hzy.symm
    omega
  have hlevelLower : a + 1 ≤ G.dist w z := by
    obtain ⟨Q, hQ⟩ := hconn.exists_walk_length_eq_dist w z
    have hQnotNil : ¬ Q.Nil := by
      intro hnil
      have hwz : w = z := hnil.eq
      exact hzw hwz.symm
    have hpenAdj : G.Adj z Q.penultimate := (Q.adj_penultimate hQnotNil).symm
    have hpen : Q.penultimate = y := hneighborUnique Q.penultimate hpenAdj
    have hdrop : G.dist w y ≤ Q.dropLast.length := by
      rw [← hpen]
      exact dist_le Q.dropLast
    have hlen := Q.length_dropLast_add_one hQnotNil
    omega
  have hlevel : G.dist w z = a + 1 := by omega
  have hcut : cutSize G {z} = 1 := by
    have hyz : y ≠ z := hzy.ne.symm
    have hdisjoint : Disjoint ({y} : Finset V) {z} := by simp [hyz]
    simp [cutSize, hneighbors, Finset.sdiff_eq_self_of_disjoint hdisjoint]
  exact ⟨z, a, ha, hset, hlevel, by simpa [hget] using hneighbors, hcut⟩

/-- A regular vertex in the pure-span branch belongs to a unique saturated
singleton block.  The block interval and its rooted BFS level are exposed
simultaneously for subsequent injectivity and layer-profile arguments. -/
theorem IsGeodesic.pureSpan_regular_vertex_geometry
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ v z : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P)
    (Cleaf : OffCorridorComponent P)
    (hleaf : offCorridorComponentFinset Cleaf = {z})
    (hothers : ∀ C : OffCorridorComponent P, C ≠ Cleaf →
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2)
    (hvOff : v ∈ offCorridorFinset P) (hvz : v ≠ z) :
    ∃ C : OffCorridorComponent P, ∃ l : ℕ,
      C ≠ Cleaf ∧
      offCorridorComponentFinset C = {v} ∧
      offCorridorComponentIntervalEdges P C = Finset.Ico l (l + 2) ∧
      G.dist w v = l + 1 := by
  classical
  have hvSupport : v ∉ P.support := by
    have := (Finset.mem_sdiff.mp hvOff).2
    simpa [supportFinset] using this
  let C := offCorridorComponentOf P v hvSupport
  have hvC : v ∈ offCorridorComponentFinset C :=
    mem_offCorridorComponentOf P hvSupport
  have hCne : C ≠ Cleaf := by
    intro hEq
    have hvLeaf : v ∈ offCorridorComponentFinset Cleaf := by
      simpa [hEq] using hvC
    have : v = z := by simpa [hleaf] using hvLeaf
    exact hvz this
  obtain ⟨hsize, hspan⟩ := hothers C hCne
  obtain ⟨l, hinterval⟩ :=
    offCorridorInterval_eq_Ico_of_card_eq_two P C hspan
  obtain ⟨c, hset, hlevel, _hleft, _hright⟩ :=
    IsGeodesic.singleton_spanTwo_geometry hconn hP C l hsize hinterval
  have hvc : v = c := by simpa [hset] using hvC
  subst c
  exact ⟨C, l, hCne, hset, hinterval, hlevel⟩

/-- Rooted levels are injective on all regular pure-span vertices.  Equality
of levels forces equality of the two length-two component intervals; two
distinct such intervals cannot coexist under overlap defect zero. -/
theorem IsGeodesic.pureSpan_regular_rootDist_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ z : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P)
    (Cleaf : OffCorridorComponent P)
    (hleaf : offCorridorComponentFinset Cleaf = {z})
    (hothers : ∀ C : OffCorridorComponent P, C ≠ Cleaf →
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2)
    (hdisjoint :
      (Set.univ : Set (OffCorridorComponent P)).PairwiseDisjoint
        (offCorridorComponentIntervalEdges P)) :
    Set.InjOn (G.dist w)
      ((offCorridorFinset P \ {z} : Finset V) : Set V) := by
  classical
  intro x hx y hy hlevel
  have hxData := Finset.mem_sdiff.mp hx
  have hyData := Finset.mem_sdiff.mp hy
  have hxz : x ≠ z := by simpa using hxData.2
  have hyz : y ≠ z := by simpa using hyData.2
  obtain ⟨Cx, lx, hCxLeaf, hCxSet, hCxInterval, hxLevel⟩ :=
    IsGeodesic.pureSpan_regular_vertex_geometry
      hconn hP Cleaf hleaf hothers hxData.1 hxz
  obtain ⟨Cy, ly, hCyLeaf, hCySet, hCyInterval, hyLevel⟩ :=
    IsGeodesic.pureSpan_regular_vertex_geometry
      hconn hP Cleaf hleaf hothers hyData.1 hyz
  by_cases hC : Cx = Cy
  · have hxMem : x ∈ offCorridorComponentFinset Cx := by simp [hCxSet]
    have hyMem : y ∈ offCorridorComponentFinset Cx := by
      simpa [hC] using (show y ∈ offCorridorComponentFinset Cy by
        simp [hCySet])
    have hxEq : x = y := by
      have hxOnly : x = x := rfl
      have hyOnly : y = x := by simpa [hCxSet] using hyMem
      exact hyOnly.symm
    exact hxEq
  · have hl : lx = ly := by omega
    have hd := hdisjoint (by simp) (by simp) hC
    have hmemX : lx ∈ offCorridorComponentIntervalEdges P Cx := by
      rw [hCxInterval]
      simp
    have hmemY : lx ∈ offCorridorComponentIntervalEdges P Cy := by
      rw [hCyInterval, ← hl]
      simp
    exact (Finset.disjoint_left.mp hd hmemX hmemY).elim

/-- No two regular pure-span vertices occupy consecutive rooted levels.
Otherwise their two-edge component intervals overlap in one corridor edge. -/
theorem IsGeodesic.pureSpan_regular_no_consecutive_levels
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ x y z : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P)
    (Cleaf : OffCorridorComponent P)
    (hleaf : offCorridorComponentFinset Cleaf = {z})
    (hothers : ∀ C : OffCorridorComponent P, C ≠ Cleaf →
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2)
    (hdisjoint :
      (Set.univ : Set (OffCorridorComponent P)).PairwiseDisjoint
        (offCorridorComponentIntervalEdges P))
    (hx : x ∈ offCorridorFinset P \ {z})
    (hy : y ∈ offCorridorFinset P \ {z})
    (hlevels : G.dist w y = G.dist w x + 1) : False := by
  classical
  have hxData := Finset.mem_sdiff.mp hx
  have hyData := Finset.mem_sdiff.mp hy
  have hxz : x ≠ z := by simpa using hxData.2
  have hyz : y ≠ z := by simpa using hyData.2
  obtain ⟨Cx, lx, _hCxLeaf, hCxSet, hCxInterval, hxLevel⟩ :=
    IsGeodesic.pureSpan_regular_vertex_geometry
      hconn hP Cleaf hleaf hothers hxData.1 hxz
  obtain ⟨Cy, ly, _hCyLeaf, hCySet, hCyInterval, hyLevel⟩ :=
    IsGeodesic.pureSpan_regular_vertex_geometry
      hconn hP Cleaf hleaf hothers hyData.1 hyz
  have hly : ly = lx + 1 := by omega
  by_cases hC : Cx = Cy
  · have hyMem : y ∈ offCorridorComponentFinset Cx := by
      simpa [hC] using (show y ∈ offCorridorComponentFinset Cy by
        simp [hCySet])
    have hyx : y = x := by simpa [hCxSet] using hyMem
    subst y
    omega
  · have hd := hdisjoint (by simp) (by simp) hC
    have hmemX : lx + 1 ∈ offCorridorComponentIntervalEdges P Cx := by
      rw [hCxInterval]
      simp
    have hmemY : lx + 1 ∈ offCorridorComponentIntervalEdges P Cy := by
      rw [hCyInterval, hly]
      simp
    exact (Finset.disjoint_left.mp hd hmemX hmemY).elim

/-- Without any injectivity assumption, a geodesic BFS layer splits into its
unique corridor vertex and the off-corridor fiber at that rooted level. -/
theorem IsGeodesic.levelLayer_card_eq_one_add_offLevelFiber_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ : V} {P : G.Walk w x₀}
    (hP : IsGeodesic P) {k : ℕ} (hk : k ≤ P.length) :
    (levelLayer (G.dist w) k).card =
      1 + (offLevelFiber P (G.dist w) k).card := by
  classical
  let off := offLevelFiber P (G.dist w) k
  have hdecomp : levelLayer (G.dist w) k = {P.getVert k} ∪ off := by
    ext v
    constructor
    · intro hv
      have hvLevel : G.dist w v = k := by simpa using hv
      by_cases hvP : v ∈ P.support
      · have hvEq := IsGeodesic.eq_getVert_of_mem_support_rootDist_eq
          hP hvP hvLevel
        simp [hvEq]
      · have hvOff : v ∈ offCorridorFinset P := by
          simp [offCorridorFinset, hvP]
        exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_filter.mpr ⟨hvOff, hvLevel⟩))
    · intro hv
      rcases Finset.mem_union.mp hv with hvPath | hvOff
      · have hvEq : v = P.getVert k := by simpa using hvPath
        subst v
        have hlevel : G.dist w (P.getVert k) = k := by
          simpa using hP.dist_getVert_eq_sub (i := 0) (j := k)
            (by omega) hk
        simpa using hlevel
      · have hvData := Finset.mem_filter.mp hvOff
        simpa [levelLayer, hvData.2]
  have hdisjoint : Disjoint ({P.getVert k} : Finset V) off := by
    rw [Finset.disjoint_left]
    intro v hvPath hvOff
    have hvEq : v = P.getVert k := by simpa using hvPath
    subst v
    have hsupport : P.getVert k ∈ supportFinset P := by simp [supportFinset]
    have hoff := (Finset.mem_filter.mp hvOff).1
    exact (Finset.mem_sdiff.mp hoff).2 hsupport
  rw [hdecomp, Finset.card_union_of_disjoint hdisjoint]
  simp [off]

/-- A demand incident with the pure-span pendant vertex exceeds the clipped
root-level threshold span by at most two.  This includes the terminal case,
where the leaf is at actual level `d+1` but is clipped to level `d`. -/
theorem IsGeodesic.pureSpan_leaf_distance_le_clippedLevelDist_add_two
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ y z : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P)
    (Cleaf : OffCorridorComponent P)
    (hleaf : offCorridorComponentFinset Cleaf = {z})
    (hothers : ∀ C : OffCorridorComponent P, C ≠ Cleaf →
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2)
    (a d : ℕ) (ha : a ≤ d) (hPd : P.length = d)
    (hzLevel : G.dist w z = a + 1)
    (hzAdj : G.Adj z (P.getVert a))
    (hyz : y ≠ z) (hyBound : G.dist w y ≤ d) :
    G.dist z y ≤
      Nat.dist (min (G.dist w z) d) (min (G.dist w y) d) + 2 := by
  classical
  let b := G.dist w y
  have hb : b ≤ d := hyBound
  have haP : a ≤ P.length := by omega
  have hzEdge : G.dist z (P.getVert a) = 1 :=
    dist_eq_one_iff_adj.mpr hzAdj
  have hyRegularAnchors := IsGeodesic.pureSpan_regular_twoSidedAnchors
    (v := y) hconn hP Cleaf hleaf hothers hyz
  by_cases htb : a + 1 ≤ b
  · have hbPos : 0 < b := by omega
    have hyPrev := hyRegularAnchors.2 hbPos
    have hab : a ≤ b - 1 := by omega
    have hbP : b - 1 ≤ P.length := by omega
    have hcorr := hP.dist_getVert_eq_sub hab hbP
    have hyEdge : G.dist (P.getVert (b - 1)) y = 1 :=
      dist_eq_one_iff_adj.mpr hyPrev
    have htri₁ := hconn.dist_triangle
      (u := z) (v := P.getVert a) (w := y)
    have htri₂ := hconn.dist_triangle
      (u := P.getVert a) (v := P.getVert (b - 1)) (w := y)
    rw [hzEdge] at htri₁
    rw [hcorr, hyEdge] at htri₂
    dsimp [b] at hb htb hcorr hyEdge ⊢
    rw [hzLevel]
    simp only [min_eq_left hyBound]
    have htLe : a + 1 ≤ d := by omega
    rw [min_eq_left htLe]
    rw [Nat.dist_eq_sub_of_le htb]
    omega
  · have hbt : b < a + 1 := by omega
    by_cases hbd : b = d
    · have had : a = d := by omega
      have hySupport : y ∈ P.support := by
        by_contra hyNot
        have hyOff : y ∈ offCorridorFinset P :=
          Finset.mem_sdiff.mpr
            ⟨Finset.mem_univ y, by simpa [supportFinset] using hyNot⟩
        obtain ⟨C, l, _hCLeaf, _hCSet, hinterval, hyLevel⟩ :=
          IsGeodesic.pureSpan_regular_vertex_geometry
            hconn hP Cleaf hleaf hothers hyOff hyz
        have hmem : l + 1 ∈ offCorridorComponentIntervalEdges P C := by
          rw [hinterval]
          simp
        have hsub := offCorridorComponentIntervalEdges_subset_range P C hmem
        have : l + 1 < d := by simpa [hPd] using Finset.mem_range.mp hsub
        dsimp [b] at hbd
        omega
      have hyEq := IsGeodesic.eq_getVert_of_mem_support_rootDist_eq
        hP hySupport (k := d) (by simpa [b, hbd])
      have hPdVert : P.getVert d = x₀ := by
        rw [← hPd]
        exact P.getVert_length
      have hyXa : y = P.getVert a := by
        rw [had]
        exact hyEq
      rw [hyXa]
      rw [hzEdge]
      omega
    · have hblt : b < d := by omega
      have hyNext := hyRegularAnchors.1 (by simpa [hPd, b] using hblt)
      have hbOneP : b + 1 ≤ P.length := by omega
      have hyEdge : G.dist (P.getVert (b + 1)) y = 1 :=
        dist_eq_one_iff_adj.mpr hyNext.symm
      by_cases hba : b < a
      · have hcorr := hP.dist_getVert_eq_sub
          (i := b + 1) (j := a) (by omega) haP
        have htri₁ := hconn.dist_triangle
          (u := z) (v := P.getVert a) (w := y)
        have htri₂ := hconn.dist_triangle
          (u := P.getVert a) (v := P.getVert (b + 1)) (w := y)
        rw [SimpleGraph.dist_comm] at hcorr
        rw [hzEdge] at htri₁
        rw [hcorr, hyEdge] at htri₂
        dsimp [b] at hb hbt hblt hba hcorr hyEdge ⊢
        rw [hzLevel]
        simp only [min_eq_left hyBound]
        by_cases had : a = d
        · subst a
          simp only [min_eq_right (by omega : d ≤ d + 1)]
          rw [Nat.dist_eq_sub_of_le_right (by omega : G.dist w y ≤ d)]
          omega
        · have htLe : a + 1 ≤ d := by omega
          rw [min_eq_left htLe]
          rw [Nat.dist_eq_sub_of_le_right (by omega : G.dist w y ≤ a + 1)]
          omega
      · have hbaEq : b = a := by omega
        have hcorr := hP.dist_getVert_eq_sub
          (i := a) (j := a + 1) (by omega) (by omega)
        have htri₁ := hconn.dist_triangle
          (u := z) (v := P.getVert a) (w := y)
        have htri₂ := hconn.dist_triangle
          (u := P.getVert a) (v := P.getVert (a + 1)) (w := y)
        have hyEdgeA : G.dist (P.getVert (a + 1)) y = 1 := by
          simpa [hbaEq] using hyEdge
        rw [hzEdge] at htri₁
        rw [hcorr, hyEdgeA] at htri₂
        dsimp [b] at hb hbt hblt hbaEq hyEdge ⊢
        rw [hzLevel, hbaEq]
        have htLe : a + 1 ≤ d := by omega
        simp only [min_eq_left htLe, min_eq_left (by omega : a ≤ d)]
        rw [Nat.dist_eq_sub_of_le_right (by omega : a ≤ a + 1)]
        omega

/-- Threshold-cut realization of the general one-row add-two matrix bound.
The caller supplies only the literal level geometry, the residual cut
capacities, and the already-audited polynomial envelope for that profile. -/
theorem totalCost_le_rlBudget_of_one_addTwo_levelCuts
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (w x₀ : V) (m₁ m₂ : I → V) (level : V → ℕ)
    (s d : ℕ) (capacity : Fin d → ℕ) (exceptional : I)
    (hroot : level w = 0) (hstub : level x₀ = d)
    (hendpoint₁ : ∀ i, level (m₁ i) ≤ d)
    (hendpoint₂ : ∀ i, level (m₂ i) ≤ d)
    (haligned : ∀ i, i ≠ exceptional →
      G.dist (m₁ i) (m₂ i) =
        Nat.dist (level (m₁ i)) (level (m₂ i)))
    (hexceptional : G.dist (m₁ exceptional) (m₂ exceptional) ≤
      Nat.dist (level (m₁ exceptional)) (level (m₂ exceptional)) + 2)
    (hRFC : ∀ T : Finset V, w ∉ T →
      (∑ i : I, separationDemand T (m₁ i) (m₂ i)) +
        (if x₀ ∈ T then 1 else 0) ≤ cutSize G T)
    (hcut : ∀ r : Fin d,
      cutSize G (levelUpperCut level r.1) ≤ capacity r + 1)
    (hlegal : ∀ i, 4 ≤ G.dist (m₁ i) (m₂ i))
    (henvelope :
      let Q := ∑ r : Fin d, ∑ q : Fin d, min (capacity r) (capacity q)
      let C := ∑ r : Fin d, capacity r
      let L := Nat.dist (level (m₁ exceptional))
        (level (m₂ exceptional))
      4 * Q + 9 * C + 16 * L + 34 ≤ 4 * rlBudget s d) :
    (∑ i : I, (G.dist (m₁ i) (m₂ i) + 1) ^ 2) ≤
      rlBudget s d := by
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
  have hthreshold : ∀ i,
      (∑ r : Fin d, cross i r) =
        Nat.dist (level (m₁ i)) (level (m₂ i)) := by
    intro i
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
    exact sum_thresholdSeparation_eq_dist
      (hendpoint₁ i) (hendpoint₂ i)
  have hmatrixAligned : ∀ i, i ≠ exceptional →
      G.dist (m₁ i) (m₂ i) = ∑ r : Fin d, cross i r := by
    intro i hie
    rw [haligned i hie, hthreshold i]
  have hmatrixExceptional :
      G.dist (m₁ exceptional) (m₂ exceptional) ≤
        (∑ r : Fin d, cross exceptional r) + 2 := by
    rw [hthreshold exceptional]
    exact hexceptional
  have hcolumn : ∀ r : Fin d,
      (∑ i : I, cross i r) ≤ capacity r := by
    intro r
    have hw : w ∉ levelUpperCut level r.1 := by simp [hroot]
    have hx : x₀ ∈ levelUpperCut level r.1 := by simp [hstub, r.2]
    have hvalid := hRFC (levelUpperCut level r.1) hw
    simp only [hx, if_true] at hvalid
    exact Nat.le_of_add_le_add_right (hvalid.trans (hcut r))
  apply totalCost_le_rlBudget_of_one_addTwo_exception
    (fun i => G.dist (m₁ i) (m₂ i)) cross capacity exceptional
    s d hcross hmatrixAligned hmatrixExceptional hcolumn hlegal
  dsimp
  dsimp at henvelope
  rw [hthreshold exceptional]
  exact henvelope

#print axioms attachment_extrema_of_interval_eq_length
#print axioms IsGeodesic.q3PureMass_levelAligned_or_candidate
#print axioms IsGeodesic.q2q2PureMass_levelAligned
#print axioms q3_exception_card_le_one
#print axioms totalCost_le_rlBudget_of_q3_zeroOrOneExceptionLevelCuts
#print axioms totalCost_le_rlBudget_of_aligned_twoHighRootLevelProfile
#print axioms totalCost_le_rlBudget_of_q3PureMass_allNonbridge_sameSide
#print axioms totalCost_le_rlBudget_of_q2q2PureMass_allNonbridge_sameSide
#print axioms IsGeodesic.singleton_spanZero_pendant_geometry

end Erdos23GapGBTwoDefectAlignment
