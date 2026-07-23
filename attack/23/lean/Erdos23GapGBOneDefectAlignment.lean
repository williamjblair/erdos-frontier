/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair, OpenAI Codex
-/
import ErdosProblems.Erdos23GapGBOneDefect
import ErdosProblems.Erdos23GapGBBinaryLayerAuto
import ErdosProblems.Erdos23GapGBOneDefectIntervals

/-!
# Erdős 23 G-B: alignment on a one-high binary layer chain

This module closes the two surviving `d=2s-1` canonical geometries.  It
derives their exact binary BFS-level profiles from the mass- and
overlap-defect interval structures, proves complete routing away from the
unique `2 x 2` layer gap and two-sided routing across it, aligns every legal
same-side demand with its BFS-level span, and lands the exact RL budget.
-/

namespace Erdos23GapGBOneDefectAlignment

open SimpleGraph
open Erdos23GapGA
open Erdos23GapGBSeries
open Erdos23GapGBJoint
open Erdos23GapGBBinaryLayers
open Erdos23GapGBBinaryLayerAuto
open Erdos23GapGBEqualityBoundary
open Erdos23GapGBOneDefect
open Erdos23GapGBOneDefectIntervals

/-- Canonical off-corridor component sizes sum to corridor slack. -/
theorem IsGeodesic.sum_offCorridorComponent_card_eq_slack
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ : V} {P : G.Walk w x₀}
    (hP : IsGeodesic P) :
    ∑ C : OffCorridorComponent P, (offCorridorComponentFinset C).card =
      slack P := by
  have hmass := sum_card_inter_offCorridorComponent P (Finset.univ : Finset V)
  simp only [Finset.inter_univ] at hmass
  rw [hmass, Finset.card_sdiff]
  simp only [Finset.inter_univ, Finset.card_univ, slack]
  have hsupp := hP.card_supportFinset
  have hle : P.length + 1 ≤ Fintype.card V := by
    rw [← hsupp]
    exact Finset.card_le_univ _
  omega

/-- On an all-nonbridge geodesic, the canonical extreme-attachment
intervals have union exactly the whole corridor edge range. -/
theorem IsGeodesic.biUnion_offCorridorIntervals_eq_range
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ : V} {P : G.Walk w x₀}
    (hP : IsGeodesic P)
    (hnonbridge : ∀ i < P.length,
      ¬G.IsBridge s(P.getVert i, P.getVert (i + 1))) :
    (Finset.univ : Finset (OffCorridorComponent P)).biUnion
        (offCorridorComponentIntervalEdges P) =
      Finset.range P.length := by
  classical
  apply Finset.Subset.antisymm
  · intro i hi
    obtain ⟨C, _hC, hiC⟩ := Finset.mem_biUnion.mp hi
    exact offCorridorComponentIntervalEdges_subset_range P C hiC
  · intro i hi
    have hiLength : i < P.length := Finset.mem_range.mp hi
    obtain ⟨C, hC⟩ :=
      hP.exists_offCorridorComponent_coversIndex_of_not_isBridge
        hiLength (hnonbridge i hiLength)
    exact Finset.mem_biUnion.mpr
      ⟨C, by simp,
        mem_offCorridorComponentIntervalEdges_of_coversIndex P C hC⟩

/-- Every nonempty canonical interval is literally `[l,l+card)`. -/
theorem offCorridorInterval_eq_Ico_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ : V} (P : G.Walk w x₀)
    (C : OffCorridorComponent P)
    (hpos : 1 ≤ (offCorridorComponentIntervalEdges P C).card) :
    ∃ l : ℕ, offCorridorComponentIntervalEdges P C =
      Finset.Ico l (l + (offCorridorComponentIntervalEdges P C).card) := by
  classical
  let A := offCorridorAttachmentIndices P C
  by_cases hA : A.Nonempty
  · let l := A.min' hA
    let h := A.max' hA
    have hinterval : offCorridorComponentIntervalEdges P C =
        Finset.Ico l h := by
      simp [offCorridorComponentIntervalEdges, A, hA, l, h]
    have hcardIco : (Finset.Ico l h).card =
        (offCorridorComponentIntervalEdges P C).card := by rw [hinterval]
    have hdiff : h - l = (offCorridorComponentIntervalEdges P C).card := by
      simpa [Nat.card_Ico] using hcardIco
    have hh : h = l + (offCorridorComponentIntervalEdges P C).card := by
      have hle := A.min'_le_max' hA
      omega
    refine ⟨l, ?_⟩
    calc
      offCorridorComponentIntervalEdges P C = Finset.Ico l h := hinterval
      _ = Finset.Ico l
          (l + (offCorridorComponentIntervalEdges P C).card) :=
        congrArg (Finset.Ico l) hh
  · have hempty : offCorridorComponentIntervalEdges P C = ∅ := by
      simp [offCorridorComponentIntervalEdges, A, hA]
    rw [hempty] at hpos
    simp at hpos

/-- Three-edge analogue of the equality-boundary attachment-extrema lemma. -/
theorem attachment_extrema_of_interval_eq_three
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ : V} (P : G.Walk w x₀)
    (C : OffCorridorComponent P) (l : ℕ)
    (hinterval : offCorridorComponentIntervalEdges P C =
      Finset.Ico l (l + 3)) :
    l ∈ offCorridorAttachmentIndices P C ∧
      l + 3 ∈ offCorridorAttachmentIndices P C ∧
      ∀ j ∈ offCorridorAttachmentIndices P C, l ≤ j ∧ j ≤ l + 3 := by
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
  have hcard : (Finset.Ico (A.min' hA) (A.max' hA)).card = 3 := by
    rw [← hdef, hinterval]
    simp
  have hdiff : A.max' hA - A.min' hA = 3 := by
    simpa [Nat.card_Ico] using hcard
  have hlmem : l ∈ Finset.Ico (A.min' hA) (A.max' hA) := by
    rw [← hdef, hinterval]
    simp
  have hl2mem : l + 2 ∈ Finset.Ico (A.min' hA) (A.max' hA) := by
    rw [← hdef, hinterval]
    simp
  have hmin : A.min' hA = l := by
    have hl := Finset.mem_Ico.mp hlmem
    have hl2 := Finset.mem_Ico.mp hl2mem
    omega
  have hmax : A.max' hA = l + 3 := by omega
  constructor
  · simpa [A, hmin] using A.min'_mem hA
  constructor
  · simpa [A, hmax] using A.max'_mem hA
  · intro j hj
    have hjA : j ∈ A := by simpa [A] using hj
    have hminLe := A.min'_le j hjA
    have hleMax := A.le_max' j hjA
    omega

/-- A singleton saturated two-edge component lies exactly on the middle BFS
level of its attachment interval. -/
theorem IsGeodesic.rootDist_singleton_spanTwo
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P)
    (C : OffCorridorComponent P) (c : V) (l : ℕ)
    (hset : offCorridorComponentFinset C = {c})
    (hinterval : offCorridorComponentIntervalEdges P C =
      Finset.Ico l (l + 2)) :
    G.dist w c = l + 1 := by
  obtain ⟨hleft, hright, _⟩ := attachment_extrema_of_interval_eq_two
    P C l hinterval
  obtain ⟨hlLength, cL, hcL, hAdjL⟩ :=
    (mem_offCorridorAttachmentIndices P C l).1 hleft
  obtain ⟨hrLength, cR, hcR, hAdjR⟩ :=
    (mem_offCorridorAttachmentIndices P C (l + 2)).1 hright
  have hcL : cL = c := by simpa [hset] using hcL
  have hcR : cR = c := by simpa [hset] using hcR
  subst cL
  subst cR
  have hleftLevel : G.dist w (P.getVert l) = l := by
    simpa using hP.dist_getVert_eq_sub (i := 0) (j := l) (by omega) hlLength
  have hrightLevel : G.dist w (P.getVert (l + 2)) = l + 2 := by
    simpa using hP.dist_getVert_eq_sub (i := 0) (j := l + 2)
      (by omega) hrLength
  have hAdjLDist : G.dist (P.getVert l) c = 1 :=
    dist_eq_one_iff_adj.mpr hAdjL.symm
  have hAdjRDist : G.dist c (P.getVert (l + 2)) = 1 :=
    dist_eq_one_iff_adj.mpr hAdjR
  have hupper := hconn.dist_triangle (u := w) (v := P.getVert l) (w := c)
  have hlower := hconn.dist_triangle (u := w) (v := c) (w := P.getVert (l + 2))
  omega

/-- Bipartiteness forbids the middle attachment of a singleton span-two
component, so its attachment indices are exactly its two extrema. -/
theorem singleton_spanTwo_attachment_iff_extreme
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ : V}
    (color : G.Coloring Bool) (P : G.Walk w x₀)
    (C : OffCorridorComponent P) (c : V) (l j : ℕ)
    (hset : offCorridorComponentFinset C = {c})
    (hinterval : offCorridorComponentIntervalEdges P C =
      Finset.Ico l (l + 2)) :
    j ∈ offCorridorAttachmentIndices P C ↔ j = l ∨ j = l + 2 := by
  obtain ⟨hleft, hright, hbounds⟩ := attachment_extrema_of_interval_eq_two
    P C l hinterval
  constructor
  · intro hj
    have hjb := hbounds j hj
    by_cases hjl : j = l
    · exact Or.inl hjl
    by_cases hjr : j = l + 2
    · exact Or.inr hjr
    have hjmid : j = l + 1 := by omega
    obtain ⟨hlLength, cL, hcL, hAdjL⟩ :=
      (mem_offCorridorAttachmentIndices P C l).1 hleft
    obtain ⟨hjLength, cJ, hcJ, hAdjJ⟩ :=
      (mem_offCorridorAttachmentIndices P C j).1 hj
    have hcL : cL = c := by simpa [hset] using hcL
    have hcJ : cJ = c := by simpa [hset] using hcJ
    subst cL
    subst cJ
    subst j
    have hPath := color.valid (P.adj_getVert_succ (i := l) (by omega))
    have hColorL := color.valid hAdjL
    have hColorJ := color.valid hAdjJ
    cases hc : color c <;>
      cases hl : color (P.getVert l) <;>
      cases hj : color (P.getVert (l + 1)) <;>
      simp_all
  · rintro (rfl | rfl)
    · exact hleft
    · exact hright

/-- A path supported on two distinct vertices is the edge between them. -/
theorem adj_of_isPath_support_subset_pair
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {a b : V}
    (W : G.Walk a b) (hW : W.IsPath) (hab : a ≠ b)
    (hsubset : supportFinset W ⊆ {a, b}) :
    G.Adj a b := by
  have hcard : (supportFinset W).card = W.length + 1 := by
    unfold supportFinset
    rw [List.toFinset_card_of_nodup hW.support_nodup, Walk.length_support]
  have hcardLe : (supportFinset W).card ≤ 2 := by
    exact (Finset.card_le_card hsubset).trans Finset.card_le_two
  have hlengthPos : 1 ≤ W.length := by
    by_contra hzero
    have hz : W.length = 0 := by omega
    exact hab (Walk.eq_of_length_eq_zero hz)
  have hlength : W.length = 1 := by omega
  exact W.adj_of_length_eq_one hlength

/-- A canonical off-corridor component with exactly two vertices contains
their edge. -/
theorem offCorridorComponent_adj_of_finset_eq_pair
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ a b : V} {P : G.Walk w x₀}
    (C : OffCorridorComponent P) (hab : a ≠ b)
    (hset : offCorridorComponentFinset C = {a, b}) :
    G.Adj a b := by
  classical
  have haC : a ∈ C := by
    rw [← mem_offCorridorComponentFinset C]
    simp [hset]
  have hbC : b ∈ C := by
    rw [← mem_offCorridorComponentFinset C]
    simp [hset]
  obtain ⟨haoff, haeq⟩ := ComponentCompl.mem_supp_iff.mp haC
  obtain ⟨hboff, hbeq⟩ := ComponentCompl.mem_supp_iff.mp hbC
  let a' : {x : V // x ∉ (supportFinset P : Set V)} := ⟨a, haoff⟩
  let b' : {x : V // x ∉ (supportFinset P : Set V)} := ⟨b, hboff⟩
  have ha' : a' ∈ ConnectedComponent.supp C :=
    (ConnectedComponent.mem_supp_iff C a').2 haeq
  have hb' : b' ∈ ConnectedComponent.supp C :=
    (ConnectedComponent.mem_supp_iff C b').2 hbeq
  obtain ⟨W, hW⟩ :=
    C.connected_toSimpleGraph.exists_isPath ⟨a', ha'⟩ ⟨b', hb'⟩
  let Woff := W.map C.toSimpleGraph_hom
  let W' : G.Walk a b :=
    (Woff.map (Embedding.induce (supportFinset P : Set V)ᶜ).toHom).copy rfl rfl
  have hWoff : Woff.IsPath :=
    Walk.map_isPath_of_injective Subtype.val_injective hW
  have hW' : W'.IsPath := by
    simpa [W'] using Walk.map_isPath_of_injective Subtype.val_injective hWoff
  have hW'C : ∀ x ∈ W'.support, x ∈ offCorridorComponentFinset C := by
    intro x hx
    change x ∈
      ((Woff.map (Embedding.induce (supportFinset P : Set V)ᶜ).toHom).copy rfl rfl).support at hx
    simp only [Walk.support_copy, Walk.support_map] at hx
    obtain ⟨xoff, hxoff, rfl⟩ := List.mem_map.mp hx
    change xoff ∈ (W.map C.toSimpleGraph_hom).support at hxoff
    rw [Walk.support_map] at hxoff
    obtain ⟨xC, _, hxC⟩ := List.mem_map.mp hxoff
    have hxval : xoff = xC.val := by simpa using hxC.symm
    rw [hxval]
    have hxeq : G.componentComplMk xC.val.prop = C :=
      (ConnectedComponent.mem_supp_iff C xC.val).1 xC.prop
    exact (mem_offCorridorComponentFinset C (x := xC.val.val)).2
      (ComponentCompl.mem_supp_iff.mpr ⟨xC.val.prop, hxeq⟩)
  apply adj_of_isPath_support_subset_pair W' hW' hab
  intro x hx
  have hxC := hW'C x (by simpa using hx)
  simpa [hset] using hxC

/-- Vertices outside the selected corridor. -/
def offCorridorFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ : V} (P : G.Walk w x₀) : Finset V :=
  Finset.univ \ supportFinset P

/-- Off-corridor vertices on one BFS level. -/
def offLevelFiber
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ : V} (P : G.Walk w x₀)
    (level : V → ℕ) (k : ℕ) : Finset V :=
  (offCorridorFinset P).filter fun v => level v = k

/-- A corridor vertex is the unique corridor-support vertex on its rooted
geodesic level. -/
theorem IsGeodesic.eq_getVert_of_mem_support_rootDist_eq
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {w x₀ v : V} {P : G.Walk w x₀} (hP : IsGeodesic P)
    {k : ℕ} (hv : v ∈ P.support) (hk : G.dist w v = k) :
    v = P.getVert k := by
  let j := P.support.idxOf v
  have hjLength : j ≤ P.length := support_idxOf_le_length P hv
  have hget : P.getVert j = v := P.getVert_support_idxOf hv
  have hjLevel : G.dist w (P.getVert j) = j := by
    simpa using hP.dist_getVert_eq_sub (i := 0) (j := j) (by omega) hjLength
  have hjk : j = k := by rw [hget, hk] at hjLevel; omega
  rw [← hget, hjk]

/-- An injective finite level map has a singleton fiber exactly on its image. -/
theorem offLevelFiber_card_eq_indicator
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ : V} (P : G.Walk w x₀)
    (level : V → ℕ) (levels : Finset ℕ)
    (hinjective : Set.InjOn level (offCorridorFinset P : Set V))
    (himage : (offCorridorFinset P).image level = levels)
    (k : ℕ) :
    (offLevelFiber P level k).card = if k ∈ levels then 1 else 0 := by
  classical
  by_cases hk : k ∈ levels
  · rw [if_pos hk]
    have hkImage : k ∈ (offCorridorFinset P).image level := by simpa [himage]
    obtain ⟨x, hxoff, hxlevel⟩ := Finset.mem_image.mp hkImage
    have hfiber : offLevelFiber P level k = {x} := by
      ext y
      constructor
      · intro hy
        have hydata := Finset.mem_filter.mp hy
        have hyx : y = x := hinjective hydata.1 hxoff (by omega)
        simp [hyx]
      · intro hy
        have hyx : y = x := by simpa using hy
        subst y
        exact Finset.mem_filter.mpr ⟨hxoff, hxlevel⟩
    simp [hfiber]
  · rw [if_neg hk]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxdata := Finset.mem_filter.mp hx
    have hxImage : level x ∈ (offCorridorFinset P).image level :=
      Finset.mem_image.mpr ⟨x, hxdata.1, rfl⟩
    have : k ∈ levels := by simpa [himage, hxdata.2] using hxImage
    exact hk this

/-- Once off-corridor BFS levels are injectively realized by `levels`, every
level on the geodesic has cardinality one plus the corresponding indicator. -/
theorem IsGeodesic.levelLayer_card_eq_one_add_indicator
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ : V} {P : G.Walk w x₀}
    (hP : IsGeodesic P) (levels : Finset ℕ)
    (hinjective : Set.InjOn (G.dist w) (offCorridorFinset P : Set V))
    (himage : (offCorridorFinset P).image (G.dist w) = levels)
    {k : ℕ} (hk : k ≤ P.length) :
    (levelLayer (G.dist w) k).card = 1 + if k ∈ levels then 1 else 0 := by
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
          simpa using hP.dist_getVert_eq_sub (i := 0) (j := k) (by omega) hk
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
  have hoffCard := offLevelFiber_card_eq_indicator
    P (G.dist w) levels hinjective himage k
  simp only [Finset.card_singleton]
  rw [show off = offLevelFiber P (G.dist w) k by rfl, hoffCard]

/-- The extreme attachment vertices of a saturated two-vertex span-three
component occupy its two internal BFS levels.  The internal adjacency is
stated explicitly; for an actual two-vertex connected component it is
automatic. -/
theorem IsGeodesic.rootDist_extrema_spanThree
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (color : G.Coloring Bool) (hP : IsGeodesic P)
    (C : OffCorridorComponent P) (a b : V) (l : ℕ)
    (hab : a ≠ b) (hset : offCorridorComponentFinset C = {a, b})
    (hinterval : offCorridorComponentIntervalEdges P C =
      Finset.Ico l (l + 3)) :
    ∃ cL cR : V,
      cL ∈ offCorridorComponentFinset C ∧
      cR ∈ offCorridorComponentFinset C ∧
      cL ≠ cR ∧ G.Adj cL cR ∧
      G.Adj cL (P.getVert l) ∧
      G.Adj cR (P.getVert (l + 3)) ∧
      G.dist w cL = l + 1 ∧ G.dist w cR = l + 2 := by
  have hAdj : G.Adj a b :=
    offCorridorComponent_adj_of_finset_eq_pair C hab hset
  obtain ⟨hleft, hright, _⟩ :=
    attachment_extrema_of_interval_eq_three P C l hinterval
  obtain ⟨hlLength, cL, hcL, hAdjL⟩ :=
    (mem_offCorridorAttachmentIndices P C l).1 hleft
  obtain ⟨hrLength, cR, hcR, hAdjR⟩ :=
    (mem_offCorridorAttachmentIndices P C (l + 3)).1 hright
  have hPath₁ := color.valid (P.adj_getVert_succ (i := l) (by omega))
  have hPath₂ := color.valid (P.adj_getVert_succ (i := l + 1) (by omega))
  have hPath₃ := color.valid (P.adj_getVert_succ (i := l + 2) (by omega))
  have hColorL := color.valid hAdjL
  have hColorR := color.valid hAdjR
  have hcLR : cL ≠ cR := by
    intro heq
    subst cR
    cases hc : color cL <;>
      cases h0 : color (P.getVert l) <;>
      cases h1 : color (P.getVert (l + 1)) <;>
      cases h2 : color (P.getVert (l + 2)) <;>
      cases h3 : color (P.getVert (l + 3)) <;>
      simp_all
  have hAdjLR : G.Adj cL cR := by
    have hcLcases : cL = a ∨ cL = b := by simpa [hset] using hcL
    have hcRcases : cR = a ∨ cR = b := by simpa [hset] using hcR
    rcases hcLcases with rfl | rfl <;> rcases hcRcases with rfl | rfl
    · exact (hcLR rfl).elim
    · exact hAdj
    · exact hAdj.symm
    · exact (hcLR rfl).elim
  have hleftLevel : G.dist w (P.getVert l) = l := by
    simpa using hP.dist_getVert_eq_sub (i := 0) (j := l) (by omega) hlLength
  have hrightLevel : G.dist w (P.getVert (l + 3)) = l + 3 := by
    simpa using hP.dist_getVert_eq_sub (i := 0) (j := l + 3)
      (by omega) hrLength
  have hAdjLDist : G.dist (P.getVert l) cL = 1 :=
    dist_eq_one_iff_adj.mpr hAdjL.symm
  have hAdjLRDist : G.dist cL cR = 1 := dist_eq_one_iff_adj.mpr hAdjLR
  have hAdjRDist : G.dist cR (P.getVert (l + 3)) = 1 :=
    dist_eq_one_iff_adj.mpr hAdjR
  have hupperL := hconn.dist_triangle (u := w) (v := P.getVert l) (w := cL)
  have htailL₁ := hconn.dist_triangle
    (u := cL) (v := cR) (w := P.getVert (l + 3))
  have hlowerL := hconn.dist_triangle
    (u := w) (v := cL) (w := P.getVert (l + 3))
  have hupperR₁ := hconn.dist_triangle (u := w) (v := cL) (w := cR)
  have hlowerR := hconn.dist_triangle
    (u := w) (v := cR) (w := P.getVert (l + 3))
  have hlevelL : G.dist w cL = l + 1 := by omega
  have hlevelR : G.dist w cR = l + 2 := by omega
  exact ⟨cL, cR, hcL, hcR, hcLR, hAdjLR, hAdjL, hAdjR,
    hlevelL, hlevelR⟩

/-- The rooted-level image of a saturated singleton component is its
one-point block interior. -/
theorem IsGeodesic.image_rootDist_singleton_spanTwo
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P)
    (C : OffCorridorComponent P) (l : ℕ)
    (hsize : (offCorridorComponentFinset C).card = 1)
    (hinterval : offCorridorComponentIntervalEdges P C =
      Finset.Ico l (l + 2)) :
    (offCorridorComponentFinset C).image (G.dist w) =
      Finset.Ioo l (l + 2) := by
  classical
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hsize
  have hlevel := IsGeodesic.rootDist_singleton_spanTwo
    hconn hP C c l hc hinterval
  ext k
  simp only [hc, Finset.image_singleton, Finset.mem_singleton]
  simp only [Finset.mem_Ioo]
  omega

/-- The rooted-level image of a saturated two-vertex component is its
two-point block interior. -/
theorem IsGeodesic.image_rootDist_pair_spanThree
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (color : G.Coloring Bool) (hP : IsGeodesic P)
    (C : OffCorridorComponent P) (l : ℕ)
    (hsize : (offCorridorComponentFinset C).card = 2)
    (hinterval : offCorridorComponentIntervalEdges P C =
      Finset.Ico l (l + 3)) :
    (offCorridorComponentFinset C).image (G.dist w) =
      Finset.Ioo l (l + 3) := by
  classical
  obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp hsize
  obtain ⟨cL, cR, hcL, hcR, hcLR, _hAdj, _hleft, _hright,
      hlevelL, hlevelR⟩ :=
    IsGeodesic.rootDist_extrema_spanThree
      hconn color hP C a b l hab hset hinterval
  have hcLcases : cL = a ∨ cL = b := by simpa [hset] using hcL
  have hcRcases : cR = a ∨ cR = b := by simpa [hset] using hcR
  have hcomponent : offCorridorComponentFinset C = {cL, cR} := by
    rcases hcLcases with hLa | hLb <;>
      rcases hcRcases with hRa | hRb
    · exact (hcLR (hLa.trans hRa.symm)).elim
    · simpa [hLa, hRb] using hset
    · simpa [hLb, hRa, Finset.pair_comm] using hset
    · exact (hcLR (hLb.trans hRb.symm)).elim
  ext k
  simp only [hcomponent, Finset.image_insert, Finset.image_singleton,
    Finset.mem_insert, Finset.mem_singleton, Finset.mem_Ioo]
  rw [hlevelL, hlevelR]
  omega

/-- A saturated singleton component is adjacent to both extreme corridor
vertices of its two-edge interval. -/
theorem singleton_spanTwo_extreme_adjacencies
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ : V} {P : G.Walk w x₀}
    (C : OffCorridorComponent P) (c : V) (l : ℕ)
    (hset : offCorridorComponentFinset C = {c})
    (hinterval : offCorridorComponentIntervalEdges P C =
      Finset.Ico l (l + 2)) :
    G.Adj c (P.getVert l) ∧ G.Adj c (P.getVert (l + 2)) := by
  obtain ⟨hleft, hright, _⟩ :=
    attachment_extrema_of_interval_eq_two P C l hinterval
  obtain ⟨_hlLength, cL, hcL, hAdjL⟩ :=
    (mem_offCorridorAttachmentIndices P C l).1 hleft
  obtain ⟨_hrLength, cR, hcR, hAdjR⟩ :=
    (mem_offCorridorAttachmentIndices P C (l + 2)).1 hright
  have hcL : cL = c := by simpa [hset] using hcL
  have hcR : cR = c := by simpa [hset] using hcR
  subst cL
  subst cR
  exact ⟨hAdjL, hAdjR⟩

/-- Every vertex is either its uniquely determined corridor vertex at the
same rooted level, or is genuinely off the corridor. -/
theorem IsGeodesic.eq_getVert_or_mem_offCorridor
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ v : V} {P : G.Walk w x₀}
    (hP : IsGeodesic P) :
    v = P.getVert (G.dist w v) ∨ v ∈ offCorridorFinset P := by
  by_cases hv : v ∈ P.support
  · exact Or.inl (IsGeodesic.eq_getVert_of_mem_support_rootDist_eq
      hP hv rfl)
  · right
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ v, by simpa [supportFinset] using hv⟩

/-- Full named geometry of a saturated singleton component. -/
theorem IsGeodesic.singleton_spanTwo_geometry
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P)
    (C : OffCorridorComponent P) (l : ℕ)
    (hsize : (offCorridorComponentFinset C).card = 1)
    (hinterval : offCorridorComponentIntervalEdges P C =
      Finset.Ico l (l + 2)) :
    ∃ c : V, offCorridorComponentFinset C = {c} ∧
      G.dist w c = l + 1 ∧
      G.Adj c (P.getVert l) ∧ G.Adj c (P.getVert (l + 2)) := by
  classical
  obtain ⟨c, hset⟩ := Finset.card_eq_one.mp hsize
  have hlevel := IsGeodesic.rootDist_singleton_spanTwo
    hconn hP C c l hset hinterval
  have hadj := singleton_spanTwo_extreme_adjacencies
    C c l hset hinterval
  exact ⟨c, hset, hlevel, hadj⟩

/-- Full named geometry of a saturated two-vertex span-three component. -/
theorem IsGeodesic.pair_spanThree_geometry
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (color : G.Coloring Bool) (hP : IsGeodesic P)
    (C : OffCorridorComponent P) (l : ℕ)
    (hsize : (offCorridorComponentFinset C).card = 2)
    (hinterval : offCorridorComponentIntervalEdges P C =
      Finset.Ico l (l + 3)) :
    ∃ cL cR : V,
      offCorridorComponentFinset C = {cL, cR} ∧ cL ≠ cR ∧
      G.Adj cL cR ∧ G.Adj cL (P.getVert l) ∧
      G.Adj cR (P.getVert (l + 3)) ∧
      G.dist w cL = l + 1 ∧ G.dist w cR = l + 2 := by
  classical
  obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp hsize
  obtain ⟨cL, cR, hcL, hcR, hcLR, hAdj, hleft, hright,
      hlevelL, hlevelR⟩ :=
    IsGeodesic.rootDist_extrema_spanThree
      hconn color hP C a b l hab hset hinterval
  have hcLcases : cL = a ∨ cL = b := by simpa [hset] using hcL
  have hcRcases : cR = a ∨ cR = b := by simpa [hset] using hcR
  have hcomponent : offCorridorComponentFinset C = {cL, cR} := by
    rcases hcLcases with hLa | hLb <;>
      rcases hcRcases with hRa | hRb
    · exact (hcLR (hLa.trans hRa.symm)).elim
    · simpa [hLa, hRb] using hset
    · simpa [hLb, hRa, Finset.pair_comm] using hset
    · exact (hcLR (hLb.trans hRb.symm)).elim
  exact ⟨cL, cR, hcomponent, hcLR, hAdj, hleft, hright,
    hlevelL, hlevelR⟩

/-- The only two canonical component shapes surviving the span-defect
elimination. -/
def hasOneDefectShape
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ : V} (P : G.Walk w x₀)
    (C : OffCorridorComponent P) : Prop :=
  (∃ l, (offCorridorComponentFinset C).card = 1 ∧
    offCorridorComponentIntervalEdges P C = Finset.Ico l (l + 2)) ∨
  (∃ l, (offCorridorComponentFinset C).card = 2 ∧
    offCorridorComponentIntervalEdges P C = Finset.Ico l (l + 3))

/-- Every vertex of a canonical complement component is off the corridor. -/
theorem mem_offCorridorFinset_of_mem_component
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ x : V} {P : G.Walk w x₀}
    {C : OffCorridorComponent P}
    (hx : x ∈ offCorridorComponentFinset C) :
    x ∈ offCorridorFinset P := by
  have hxComp : x ∈ C := (mem_offCorridorComponentFinset C).1 hx
  obtain ⟨hxnot, _⟩ := ComponentCompl.mem_supp_iff.mp hxComp
  exact Finset.mem_sdiff.mpr
    ⟨Finset.mem_univ x, by simpa [supportFinset] using hxnot⟩

/-- A span-three pair forces the unique adjacent doubled-level gap to be
its middle gap. -/
theorem IsGeodesic.high_eq_leftInterior_of_pair_spanThree
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (color : G.Coloring Bool) (hP : IsGeodesic P)
    (levels : Finset ℕ) (high : ℕ)
    (himage : (offCorridorFinset P).image (G.dist w) = levels)
    (hunique : ∀ r, r < P.length → r ∈ levels →
      r + 1 ∈ levels → r = high)
    (C : OffCorridorComponent P) (l : ℕ)
    (hsize : (offCorridorComponentFinset C).card = 2)
    (hinterval : offCorridorComponentIntervalEdges P C =
      Finset.Ico l (l + 3)) :
    l + 1 = high := by
  obtain ⟨cL, cR, hset, _hne, _hadj, _hleft, _hright,
      hlevelL, hlevelR⟩ :=
    IsGeodesic.pair_spanThree_geometry
      hconn color hP C l hsize hinterval
  have hcL : cL ∈ offCorridorFinset P := by
    apply mem_offCorridorFinset_of_mem_component (C := C)
    rw [hset]
    simp
  have hcR : cR ∈ offCorridorFinset P := by
    apply mem_offCorridorFinset_of_mem_component (C := C)
    rw [hset]
    simp
  have hlE : l + 1 ∈ levels := by
    rw [← himage]
    exact Finset.mem_image.mpr ⟨cL, hcL, hlevelL⟩
  have hrE : l + 2 ∈ levels := by
    rw [← himage]
    exact Finset.mem_image.mpr ⟨cR, hcR, hlevelR⟩
  have hlmem : l + 1 ∈ offCorridorComponentIntervalEdges P C := by
    rw [hinterval]
    simp
  have hllt : l + 1 < P.length := Finset.mem_range.mp
    (offCorridorComponentIntervalEdges_subset_range P C hlmem)
  exact hunique (l + 1) hllt hlE (by simpa [Nat.add_assoc] using hrE)

/-- Off-corridor vertices cross every ordinary gap to the right. -/
theorem IsGeodesic.offVertex_adj_next_of_oneDefectShapes
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ x : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (color : G.Coloring Bool) (hP : IsGeodesic P)
    (levels : Finset ℕ) (high r : ℕ)
    (himage : (offCorridorFinset P).image (G.dist w) = levels)
    (hunique : ∀ q, q < P.length → q ∈ levels →
      q + 1 ∈ levels → q = high)
    (hshape : ∀ C : OffCorridorComponent P, hasOneDefectShape P C)
    (hxoff : x ∈ offCorridorFinset P) (hxlevel : G.dist w x = r)
    (hrne : r ≠ high) :
    G.Adj x (P.getVert (r + 1)) := by
  classical
  have hxnot : x ∉ P.support := by
    have := (Finset.mem_sdiff.mp hxoff).2
    simpa [supportFinset] using this
  let C := offCorridorComponentOf P x hxnot
  have hxC : x ∈ offCorridorComponentFinset C :=
    mem_offCorridorComponentOf P hxnot
  rcases hshape C with ⟨l, hsize, hinterval⟩ | ⟨l, hsize, hinterval⟩
  · obtain ⟨c, hset, hlevel, _hleft, hright⟩ :=
      IsGeodesic.singleton_spanTwo_geometry hconn hP C l hsize hinterval
    have hxc : x = c := by simpa [hset] using hxC
    subst x
    have hr : r = l + 1 := by omega
    simpa [hr, Nat.add_assoc] using hright
  · obtain ⟨cL, cR, hset, _hne, _hadj, _hleft, hright,
        hlevelL, hlevelR⟩ :=
      IsGeodesic.pair_spanThree_geometry
        hconn color hP C l hsize hinterval
    have hhigh : l + 1 = high :=
      IsGeodesic.high_eq_leftInterior_of_pair_spanThree
        hconn color hP levels high himage hunique C l hsize hinterval
    have hxc : x = cL ∨ x = cR := by simpa [hset] using hxC
    rcases hxc with rfl | rfl
    · have : r = high := by omega
      exact (hrne this).elim
    · have hr : r = l + 2 := by omega
      simpa [hr, Nat.add_assoc] using hright

/-- Off-corridor vertices cross every ordinary gap to the left. -/
theorem IsGeodesic.offVertex_adj_prev_of_oneDefectShapes
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ x : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (color : G.Coloring Bool) (hP : IsGeodesic P)
    (levels : Finset ℕ) (high r : ℕ)
    (himage : (offCorridorFinset P).image (G.dist w) = levels)
    (hunique : ∀ q, q < P.length → q ∈ levels →
      q + 1 ∈ levels → q = high)
    (hshape : ∀ C : OffCorridorComponent P, hasOneDefectShape P C)
    (hxoff : x ∈ offCorridorFinset P) (hxlevel : G.dist w x = r + 1)
    (hrne : r ≠ high) :
    G.Adj (P.getVert r) x := by
  classical
  have hxnot : x ∉ P.support := by
    have := (Finset.mem_sdiff.mp hxoff).2
    simpa [supportFinset] using this
  let C := offCorridorComponentOf P x hxnot
  have hxC : x ∈ offCorridorComponentFinset C :=
    mem_offCorridorComponentOf P hxnot
  rcases hshape C with ⟨l, hsize, hinterval⟩ | ⟨l, hsize, hinterval⟩
  · obtain ⟨c, hset, hlevel, hleft, _hright⟩ :=
      IsGeodesic.singleton_spanTwo_geometry hconn hP C l hsize hinterval
    have hxc : x = c := by simpa [hset] using hxC
    subst x
    have hr : r = l := by omega
    simpa [hr] using hleft.symm
  · obtain ⟨cL, cR, hset, _hne, _hadj, hleft, _hright,
        hlevelL, hlevelR⟩ :=
      IsGeodesic.pair_spanThree_geometry
        hconn color hP C l hsize hinterval
    have hhigh : l + 1 = high :=
      IsGeodesic.high_eq_leftInterior_of_pair_spanThree
        hconn color hP levels high himage hunique C l hsize hinterval
    have hxc : x = cL ∨ x = cR := by simpa [hset] using hxC
    rcases hxc with rfl | rfl
    · have hr : r = l := by omega
      simpa [hr] using hleft.symm
    · have : r = high := by omega
      exact (hrne this).elim

/-- Mass-defect arithmetic plus span saturation yields exactly the two
canonical component shapes. -/
theorem componentShapes_of_massDefect
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ : V} (P : G.Walk w x₀)
    (components : Finset (OffCorridorComponent P))
    (hall : ∀ C, C ∈ components)
    (hpositive : ∀ C ∈ components,
      1 ≤ (offCorridorComponentFinset C).card)
    (hmass : ∑ C ∈ components,
      (offCorridorComponentFinset C).card = slack P)
    (hspan : ∀ C ∈ components,
      (offCorridorComponentIntervalEdges P C).card ≤
        (offCorridorComponentFinset C).card + 1)
    (hmassOne : massDefect components (slack P) = 1)
    (hspanZero : spanDefect components
      (fun C => (offCorridorComponentFinset C).card)
      (fun C => (offCorridorComponentIntervalEdges P C).card) = 0) :
    ∀ C, hasOneDefectShape P C := by
  classical
  let size : OffCorridorComponent P → ℕ := fun C =>
    (offCorridorComponentFinset C).card
  let span : OffCorridorComponent P → ℕ := fun C =>
    (offCorridorComponentIntervalEdges P C).card
  obtain ⟨hsizeLe, _hbig⟩ := massDefect_structure components size
    (slack P) (by simpa [size] using hpositive)
    (by simpa [size] using hmass) hmassOne
  have hsaturated := all_span_saturated_of_spanDefect_eq_zero
    components size span (by simpa [size, span] using hspan)
    (by simpa [size, span] using hspanZero)
  intro C
  have hC := hall C
  have hpos := hpositive C hC
  have hle := hsizeLe C hC
  have hsat := hsaturated C hC
  have hinterPos : 1 ≤ (offCorridorComponentIntervalEdges P C).card := by
    change 1 ≤ span C
    omega
  obtain ⟨l, hinterval⟩ := offCorridorInterval_eq_Ico_card P C hinterPos
  by_cases hunit : (offCorridorComponentFinset C).card = 1
  · left
    refine ⟨l, hunit, ?_⟩
    have hunit' : size C = 1 := by simpa [size] using hunit
    have hspanTwo : span C = 2 := by omega
    change offCorridorComponentIntervalEdges P C =
      Finset.Ico l (l + span C) at hinterval
    rw [hspanTwo] at hinterval
    exact hinterval
  · right
    have hpair' : size C = 2 := by
      have hsizeEq : size C = (offCorridorComponentFinset C).card := rfl
      omega
    have hpair : (offCorridorComponentFinset C).card = 2 := by
      simpa [size] using hpair'
    refine ⟨l, hpair, ?_⟩
    have hspanThree : span C = 3 := by omega
    change offCorridorComponentIntervalEdges P C =
      Finset.Ico l (l + span C) at hinterval
    rw [hspanThree] at hinterval
    exact hinterval

/-- Overlap-defect arithmetic makes every component a saturated singleton
two-edge interval, hence in particular a one-defect shape. -/
theorem componentShapes_of_overlapDefect
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ : V} (P : G.Walk w x₀)
    (components : Finset (OffCorridorComponent P))
    (hall : ∀ C, C ∈ components)
    (hpositive : ∀ C ∈ components,
      1 ≤ (offCorridorComponentFinset C).card)
    (hmass : ∑ C ∈ components,
      (offCorridorComponentFinset C).card = slack P)
    (hspan : ∀ C ∈ components,
      (offCorridorComponentIntervalEdges P C).card ≤
        (offCorridorComponentFinset C).card + 1)
    (hmassZero : massDefect components (slack P) = 0)
    (hspanZero : spanDefect components
      (fun C => (offCorridorComponentFinset C).card)
      (fun C => (offCorridorComponentIntervalEdges P C).card) = 0) :
    ∀ C, hasOneDefectShape P C := by
  classical
  let size : OffCorridorComponent P → ℕ := fun C =>
    (offCorridorComponentFinset C).card
  let span : OffCorridorComponent P → ℕ := fun C =>
    (offCorridorComponentIntervalEdges P C).card
  have hunit := massDefect_zero_forces_unit_sizes components size
    (slack P) (by simpa [size] using hpositive)
    (by simpa [size] using hmass) hmassZero
  have hsaturated := all_span_saturated_of_spanDefect_eq_zero
    components size span (by simpa [size, span] using hspan)
    (by simpa [size, span] using hspanZero)
  intro C
  have hC := hall C
  have hsizeC := hunit C hC
  have hspanC := hsaturated C hC
  have hinterPos : 1 ≤ (offCorridorComponentIntervalEdges P C).card := by
    change 1 ≤ span C
    omega
  obtain ⟨l, hinterval⟩ := offCorridorInterval_eq_Ico_card P C hinterPos
  left
  refine ⟨l, by simpa [size] using hsizeC, ?_⟩
  have hspanTwo : span C = 2 := by omega
  change offCorridorComponentIntervalEdges P C =
    Finset.Ico l (l + span C) at hinterval
  rw [hspanTwo] at hinterval
  exact hinterval

/-- Every off-corridor vertex in a canonical one-defect component is within
two steps of the corridor vertex on the same BFS level. -/
theorem IsGeodesic.offVertex_dist_sameLevelCorridor_le_two
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ x : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (color : G.Coloring Bool) (hP : IsGeodesic P)
    (hshape : ∀ C : OffCorridorComponent P, hasOneDefectShape P C)
    (hxoff : x ∈ offCorridorFinset P) :
    G.dist x (P.getVert (G.dist w x)) ≤ 2 := by
  classical
  have hxnot : x ∉ P.support := by
    have := (Finset.mem_sdiff.mp hxoff).2
    simpa [supportFinset] using this
  let C := offCorridorComponentOf P x hxnot
  have hxC : x ∈ offCorridorComponentFinset C :=
    mem_offCorridorComponentOf P hxnot
  rcases hshape C with ⟨l, hsize, hinterval⟩ | ⟨l, hsize, hinterval⟩
  · obtain ⟨c, hset, hlevel, hleft, _hright⟩ :=
      IsGeodesic.singleton_spanTwo_geometry hconn hP C l hsize hinterval
    have hxc : x = c := by simpa [hset] using hxC
    subst x
    have hlmem : l ∈ offCorridorComponentIntervalEdges P C := by
      rw [hinterval]
      simp
    have hllt : l < P.length := Finset.mem_range.mp
      (offCorridorComponentIntervalEdges_subset_range P C hlmem)
    have hpath : G.Adj (P.getVert l) (P.getVert (l + 1)) :=
      P.adj_getVert_succ hllt
    have hleftDist : G.dist c (P.getVert l) = 1 :=
      dist_eq_one_iff_adj.mpr hleft
    have hpathDist : G.dist (P.getVert l) (P.getVert (l + 1)) = 1 :=
      dist_eq_one_iff_adj.mpr hpath
    have htri := hconn.dist_triangle
      (u := c) (v := P.getVert l) (w := P.getVert (l + 1))
    simpa [hlevel] using (by omega :
      G.dist c (P.getVert (l + 1)) ≤ 2)
  · obtain ⟨cL, cR, hset, _hne, _hadj, hleft, hright,
        hlevelL, hlevelR⟩ :=
      IsGeodesic.pair_spanThree_geometry
        hconn color hP C l hsize hinterval
    have hxc : x = cL ∨ x = cR := by simpa [hset] using hxC
    rcases hxc with hxc | hxc
    · subst x
      have hlmem : l ∈ offCorridorComponentIntervalEdges P C := by
        rw [hinterval]
        simp
      have hllt : l < P.length := Finset.mem_range.mp
        (offCorridorComponentIntervalEdges_subset_range P C hlmem)
      have hpath : G.Adj (P.getVert l) (P.getVert (l + 1)) :=
        P.adj_getVert_succ hllt
      have hleftDist : G.dist cL (P.getVert l) = 1 :=
        dist_eq_one_iff_adj.mpr hleft
      have hpathDist : G.dist (P.getVert l) (P.getVert (l + 1)) = 1 :=
        dist_eq_one_iff_adj.mpr hpath
      have htri := hconn.dist_triangle
        (u := cL) (v := P.getVert l) (w := P.getVert (l + 1))
      simpa [hlevelL] using (by omega :
        G.dist cL (P.getVert (l + 1)) ≤ 2)
    · subst x
      have hl2mem : l + 2 ∈ offCorridorComponentIntervalEdges P C := by
        rw [hinterval]
        simp
      have hl2lt : l + 2 < P.length := Finset.mem_range.mp
        (offCorridorComponentIntervalEdges_subset_range P C hl2mem)
      have hpath : G.Adj (P.getVert (l + 2)) (P.getVert (l + 3)) :=
        P.adj_getVert_succ hl2lt
      have hrightDist : G.dist cR (P.getVert (l + 3)) = 1 :=
        dist_eq_one_iff_adj.mpr hright
      have hpathDist : G.dist (P.getVert (l + 3)) (P.getVert (l + 2)) = 1 :=
        dist_eq_one_iff_adj.mpr hpath.symm
      have htri := hconn.dist_triangle
        (u := cR) (v := P.getVert (l + 3)) (w := P.getVert (l + 2))
      simpa [hlevelR] using (by omega :
        G.dist cR (P.getVert (l + 2)) ≤ 2)

/-- Canonical off-corridor vertices lie on strict interior corridor levels. -/
theorem IsGeodesic.offVertex_rootDist_lt_length_of_shape
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ x : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (color : G.Coloring Bool) (hP : IsGeodesic P)
    (hshape : ∀ C : OffCorridorComponent P, hasOneDefectShape P C)
    (hxoff : x ∈ offCorridorFinset P) :
    G.dist w x < P.length := by
  classical
  have hxnot : x ∉ P.support := by
    have := (Finset.mem_sdiff.mp hxoff).2
    simpa [supportFinset] using this
  let C := offCorridorComponentOf P x hxnot
  have hxC : x ∈ offCorridorComponentFinset C :=
    mem_offCorridorComponentOf P hxnot
  rcases hshape C with ⟨l, hsize, hinterval⟩ | ⟨l, hsize, hinterval⟩
  · obtain ⟨c, hset, hlevel, _hleft, _hright⟩ :=
      IsGeodesic.singleton_spanTwo_geometry hconn hP C l hsize hinterval
    have hxc : x = c := by simpa [hset] using hxC
    subst x
    have hmem : l + 1 ∈ offCorridorComponentIntervalEdges P C := by
      rw [hinterval]
      simp
    have := Finset.mem_range.mp
      (offCorridorComponentIntervalEdges_subset_range P C hmem)
    omega
  · obtain ⟨cL, cR, hset, _hne, _hadj, _hleft, _hright,
        hlevelL, hlevelR⟩ :=
      IsGeodesic.pair_spanThree_geometry
        hconn color hP C l hsize hinterval
    have hxc : x = cL ∨ x = cR := by simpa [hset] using hxC
    rcases hxc with hxc | hxc
    · subst x
      have hmem : l + 1 ∈ offCorridorComponentIntervalEdges P C := by
        rw [hinterval]
        simp
      have := Finset.mem_range.mp
        (offCorridorComponentIntervalEdges_subset_range P C hmem)
      omega
    · subst x
      have hmem : l + 2 ∈ offCorridorComponentIntervalEdges P C := by
        rw [hinterval]
        simp
      have := Finset.mem_range.mp
        (offCorridorComponentIntervalEdges_subset_range P C hmem)
      omega

/-- Every vertex of a one-defect canonical graph lies within the rooted
corridor depth. -/
theorem IsGeodesic.rootDist_le_length_of_componentShapes
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (color : G.Coloring Bool) (hP : IsGeodesic P)
    (hshape : ∀ C : OffCorridorComponent P, hasOneDefectShape P C) :
    ∀ v : V, G.dist w v ≤ P.length := by
  intro v
  by_cases hv : v ∈ P.support
  · let j := P.support.idxOf v
    have hj : j ≤ P.length := support_idxOf_le_length P hv
    have hget : P.getVert j = v := P.getVert_support_idxOf hv
    have hlevel : G.dist w (P.getVert j) = j := by
      simpa using hP.dist_getVert_eq_sub (i := 0) (j := j) (by omega) hj
    rw [hget] at hlevel
    omega
  · have hvoff : v ∈ offCorridorFinset P :=
      Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ v, by simpa [supportFinset] using hv⟩
    exact (IsGeodesic.offVertex_rootDist_lt_length_of_shape
      hconn color hP hshape hvoff).le

/-- Canonical one-defect component shapes plus the unique adjacent doubled
levels imply all four local hypotheses of the one-high routing theorem. -/
theorem IsGeodesic.localOneHighGeometry_of_componentShapes
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (color : G.Coloring Bool) (hP : IsGeodesic P)
    (levels : Finset ℕ) (high : ℕ)
    (hhigh : high < P.length ∧ high ∈ levels ∧ high + 1 ∈ levels)
    (hunique : ∀ r, r < P.length → r ∈ levels →
      r + 1 ∈ levels → r = high)
    (himage : (offCorridorFinset P).image (G.dist w) = levels)
    (hinjective : Set.InjOn (G.dist w) (offCorridorFinset P : Set V))
    (hshape : ∀ C : OffCorridorComponent P, hasOneDefectShape P C) :
    (∀ {r : ℕ}, r < P.length → r ≠ high →
        ∀ {u v : V}, G.dist w u = r → G.dist w v = r + 1 → G.Adj u v) ∧
      (∀ u : V, G.dist w u = high →
        ∃ v : V, G.dist w v = high + 1 ∧ G.Adj u v) ∧
      (∀ v : V, G.dist w v = high + 1 →
        ∃ u : V, G.dist w u = high ∧ G.Adj u v) ∧
      (∀ {u v : V}, G.dist w u = G.dist w v → G.dist u v ≤ 2) := by
  classical
  have hlow : ∀ {r : ℕ}, r < P.length → r ≠ high →
      ∀ {u v : V}, G.dist w u = r → G.dist w v = r + 1 →
        G.Adj u v := by
    intro r hrlt hrne u v huLevel hvLevel
    rcases IsGeodesic.eq_getVert_or_mem_offCorridor hP (v := u) with hu | hu
    · have huEq : u = P.getVert r := by simpa [huLevel] using hu
      rcases IsGeodesic.eq_getVert_or_mem_offCorridor hP (v := v) with hv | hv
      · have hvEq : v = P.getVert (r + 1) := by simpa [hvLevel] using hv
        subst u
        subst v
        exact P.adj_getVert_succ hrlt
      · subst u
        exact IsGeodesic.offVertex_adj_prev_of_oneDefectShapes
          hconn color hP levels high r himage hunique hshape hv hvLevel hrne
    · rcases IsGeodesic.eq_getVert_or_mem_offCorridor hP (v := v) with hv | hv
      · have hvEq : v = P.getVert (r + 1) := by simpa [hvLevel] using hv
        subst v
        exact IsGeodesic.offVertex_adj_next_of_oneDefectShapes
          hconn color hP levels high r himage hunique hshape hu huLevel hrne
      · have huE : r ∈ levels := by
          rw [← himage]
          exact Finset.mem_image.mpr ⟨u, hu, huLevel⟩
        have hvE : r + 1 ∈ levels := by
          rw [← himage]
          exact Finset.mem_image.mpr ⟨v, hv, hvLevel⟩
        exact (hrne (hunique r hrlt huE hvE)).elim
  have hforward : ∀ u : V, G.dist w u = high →
      ∃ v : V, G.dist w v = high + 1 ∧ G.Adj u v := by
    intro u huLevel
    rcases IsGeodesic.eq_getVert_or_mem_offCorridor hP (v := u) with hu | hu
    · have huEq : u = P.getVert high := by simpa [huLevel] using hu
      subst u
      refine ⟨P.getVert (high + 1), ?_, P.adj_getVert_succ hhigh.1⟩
      simpa using hP.dist_getVert_eq_sub (i := 0) (j := high + 1)
        (by omega) (by omega)
    · have hunot : u ∉ P.support := by
        have := (Finset.mem_sdiff.mp hu).2
        simpa [supportFinset] using this
      let C := offCorridorComponentOf P u hunot
      have huC : u ∈ offCorridorComponentFinset C :=
        mem_offCorridorComponentOf P hunot
      rcases hshape C with ⟨l, hsize, hinterval⟩ | ⟨l, hsize, hinterval⟩
      · obtain ⟨c, hset, hlevel, _hleft, hright⟩ :=
          IsGeodesic.singleton_spanTwo_geometry hconn hP C l hsize hinterval
        have huc : u = c := by simpa [hset] using huC
        subst u
        have hh : high = l + 1 := by omega
        refine ⟨P.getVert (l + 2), ?_, ?_⟩
        · have hroot : G.dist w (P.getVert (l + 2)) = l + 2 := by
            simpa using hP.dist_getVert_eq_sub (i := 0) (j := l + 2)
              (by omega) (by omega)
          omega
        · exact hright
      · obtain ⟨cL, cR, hset, _hne, hadj, _hleft, _hright,
            hlevelL, hlevelR⟩ :=
          IsGeodesic.pair_spanThree_geometry
            hconn color hP C l hsize hinterval
        have hh : l + 1 = high :=
          IsGeodesic.high_eq_leftInterior_of_pair_spanThree
            hconn color hP levels high himage hunique C l hsize hinterval
        have huc : u = cL ∨ u = cR := by simpa [hset] using huC
        rcases huc with rfl | rfl
        · exact ⟨cR, by omega, hadj⟩
        · exfalso
          omega
  have hbackward : ∀ v : V, G.dist w v = high + 1 →
      ∃ u : V, G.dist w u = high ∧ G.Adj u v := by
    intro v hvLevel
    rcases IsGeodesic.eq_getVert_or_mem_offCorridor hP (v := v) with hv | hv
    · have hvEq : v = P.getVert (high + 1) := by simpa [hvLevel] using hv
      subst v
      refine ⟨P.getVert high, ?_, P.adj_getVert_succ hhigh.1⟩
      simpa using hP.dist_getVert_eq_sub (i := 0) (j := high)
        (by omega) hhigh.1.le
    · have hvnot : v ∉ P.support := by
        have := (Finset.mem_sdiff.mp hv).2
        simpa [supportFinset] using this
      let C := offCorridorComponentOf P v hvnot
      have hvC : v ∈ offCorridorComponentFinset C :=
        mem_offCorridorComponentOf P hvnot
      rcases hshape C with ⟨l, hsize, hinterval⟩ | ⟨l, hsize, hinterval⟩
      · obtain ⟨c, hset, hlevel, hleft, _hright⟩ :=
          IsGeodesic.singleton_spanTwo_geometry hconn hP C l hsize hinterval
        have hvc : v = c := by simpa [hset] using hvC
        subst v
        have hh : high = l := by omega
        refine ⟨P.getVert l, ?_, ?_⟩
        · have hroot : G.dist w (P.getVert l) = l := by
            simpa using hP.dist_getVert_eq_sub (i := 0) (j := l)
              (by omega) (by omega)
          omega
        · exact hleft.symm
      · obtain ⟨cL, cR, hset, _hne, hadj, _hleft, _hright,
            hlevelL, hlevelR⟩ :=
          IsGeodesic.pair_spanThree_geometry
            hconn color hP C l hsize hinterval
        have hh : l + 1 = high :=
          IsGeodesic.high_eq_leftInterior_of_pair_spanThree
            hconn color hP levels high himage hunique C l hsize hinterval
        have hvc : v = cL ∨ v = cR := by simpa [hset] using hvC
        rcases hvc with rfl | rfl
        · exfalso
          omega
        · exact ⟨cL, by omega, hadj⟩
  have hsameLayer : ∀ {u v : V}, G.dist w u = G.dist w v →
      G.dist u v ≤ 2 := by
    intro u v huv
    rcases IsGeodesic.eq_getVert_or_mem_offCorridor hP (v := u) with hu | hu
    · rcases IsGeodesic.eq_getVert_or_mem_offCorridor hP (v := v) with hv | hv
      · have huvEq : u = v := by
          calc
            u = P.getVert (G.dist w u) := hu
            _ = P.getVert (G.dist w v) := by rw [huv]
            _ = v := hv.symm
        subst v
        simp
      · have hvClose := IsGeodesic.offVertex_dist_sameLevelCorridor_le_two
          hconn color hP hshape hv
        have huEq : u = P.getVert (G.dist w v) := by simpa [huv] using hu
        subst u
        simpa [SimpleGraph.dist_comm] using hvClose
    · rcases IsGeodesic.eq_getVert_or_mem_offCorridor hP (v := v) with hv | hv
      · have huClose := IsGeodesic.offVertex_dist_sameLevelCorridor_le_two
          hconn color hP hshape hu
        have hvEq : v = P.getVert (G.dist w u) := by simpa [← huv] using hv
        subst v
        exact huClose
      · have huvEq : u = v := hinjective hu hv huv
        subst v
        simp
  exact ⟨hlow, hforward, hbackward, hsameLayer⟩

/-- In the canonical mass-defect alternative, the off-corridor vertices
occupy exactly the strict interiors of the disjoint saturated component
intervals.  Consequently their rooted levels are injective, there are
`slack P` doubled levels, every corridor gap is active, and exactly one gap
has both endpoint levels doubled. -/
theorem IsGeodesic.massDefect_rootLevelProfile
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (color : G.Coloring Bool) (hP : IsGeodesic P)
    (hs : 1 ≤ slack P) (hone : P.length = 2 * slack P - 1)
    (hnonbridge : ∀ i < P.length,
      ¬G.IsBridge s(P.getVert i, P.getVert (i + 1)))
    (hmassOne : massDefect
      (Finset.univ : Finset (OffCorridorComponent P)) (slack P) = 1)
    (hspanZero : spanDefect
      (Finset.univ : Finset (OffCorridorComponent P))
      (fun C => (offCorridorComponentFinset C).card)
      (fun C => (offCorridorComponentIntervalEdges P C).card) = 0)
    (hoverlapZero : overlapDefect
      (Finset.univ : Finset (OffCorridorComponent P))
      (fun C => (offCorridorComponentIntervalEdges P C).card)
      ((Finset.univ : Finset (OffCorridorComponent P)).biUnion
        (offCorridorComponentIntervalEdges P)).card = 0) :
    ∃ levels : Finset ℕ,
      levels.card = slack P ∧
      (∀ r < P.length, r ∈ levels ∨ r + 1 ∈ levels) ∧
      (∃! r, r < P.length ∧ r ∈ levels ∧ r + 1 ∈ levels) ∧
      (offCorridorFinset P).image (G.dist w) = levels ∧
      Set.InjOn (G.dist w) (offCorridorFinset P : Set V) := by
  classical
  let components : Finset (OffCorridorComponent P) := Finset.univ
  let size : OffCorridorComponent P → ℕ := fun C =>
    (offCorridorComponentFinset C).card
  let interval : OffCorridorComponent P → Finset ℕ :=
    offCorridorComponentIntervalEdges P
  let len : OffCorridorComponent P → ℕ := fun C => (interval C).card
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
    apply all_span_saturated_of_spanDefect_eq_zero components size len hspan
    simpa [components, size, len, interval] using hspanZero
  obtain ⟨hsizeLe, hbigSize⟩ := massDefect_structure
    components size (slack P) hpositive hmass (by
      simpa [components] using hmassOne)
  have hintervalPos : ∀ C, 1 ≤ (interval C).card := by
    intro C
    have hpos := hpositive C (by simp [components])
    have hsat := hsaturated C (by simp [components])
    change 1 ≤ len C
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
      Finset.range (2 * slack P - 1) := by
    have hfamily : blockInterval lo len = interval := by
      funext C
      exact (hlo C).symm
    rw [← hone]
    rw [hfamily]
    exact hunionActual
  have hdisjointActual : (components : Set (OffCorridorComponent P)).PairwiseDisjoint
      interval := by
    apply pairwiseDisjoint_of_overlapDefect_eq_zero components interval
    simpa [components, interval, len] using hoverlapZero
  have hdisjoint : (components : Set (OffCorridorComponent P)).PairwiseDisjoint
      (blockInterval lo len) := by
    have hfamily : blockInterval lo len = interval := by
      funext C
      exact (hlo C).symm
    rw [hfamily]
    exact hdisjointActual
  have hlen : ∀ C ∈ components, len C = 2 ∨ len C = 3 := by
    intro C hC
    have hpos := hpositive C hC
    have hle := hsizeLe C hC
    have hsat := hsaturated C hC
    omega
  have hbigLen : ∃! C, C ∈ components ∧ len C = 3 := by
    obtain ⟨C, hC, huniq⟩ := hbigSize
    refine ⟨C, ⟨hC.1, ?_⟩, ?_⟩
    · rw [hsaturated C hC.1, hC.2]
    · intro D hD
      apply huniq D
      refine ⟨hD.1, ?_⟩
      have hpos := hpositive D hD.1
      have hsat := hsaturated D hD.1
      omega
  let levels := interiorLevels components lo len
  obtain ⟨hlevelsCard, hactive, hhigh⟩ :=
    massIntervalProfile components lo len (slack P)
      hunion hdisjoint hlen hbigLen
  have himageComponent : ∀ C,
      (offCorridorComponentFinset C).image (G.dist w) =
        blockInterior lo len C := by
    intro C
    have hC : C ∈ components := by simp [components]
    have hpos := hpositive C hC
    have hle := hsizeLe C hC
    have hsat := hsaturated C hC
    have hinterval := hlo C
    by_cases hunit : size C = 1
    · have hlenC : len C = 2 := by omega
      have hspanTwo : interval C = Finset.Ico (lo C) (lo C + 2) := by
        simpa [blockInterval, hlenC] using hinterval
      simpa [size, interval, blockInterior, hlenC] using
        IsGeodesic.image_rootDist_singleton_spanTwo
          hconn hP C (lo C) hunit hspanTwo
    · have hpair : size C = 2 := by omega
      have hlenC : len C = 3 := by omega
      have hspanThree : interval C = Finset.Ico (lo C) (lo C + 3) := by
        simpa [blockInterval, hlenC] using hinterval
      simpa [size, interval, blockInterior, hlenC] using
        IsGeodesic.image_rootDist_pair_spanThree
          hconn color hP C (lo C) hpair hspanThree
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
  exact ⟨levels, hlevelsCard, by simpa [levels, hone] using hactive,
    by simpa [levels, hone] using hhigh, himage, hinjective⟩

/-- The analogous rooted-level profile in the overlap-defect alternative.
Here every component is a saturated singleton two-edge interval; their
midpoints are the doubled BFS levels. -/
theorem IsGeodesic.overlapDefect_rootLevelProfile
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P)
    (hs : 1 ≤ slack P) (hone : P.length = 2 * slack P - 1)
    (hnonbridge : ∀ i < P.length,
      ¬G.IsBridge s(P.getVert i, P.getVert (i + 1)))
    (hmassZero : massDefect
      (Finset.univ : Finset (OffCorridorComponent P)) (slack P) = 0)
    (hspanZero : spanDefect
      (Finset.univ : Finset (OffCorridorComponent P))
      (fun C => (offCorridorComponentFinset C).card)
      (fun C => (offCorridorComponentIntervalEdges P C).card) = 0)
    (hoverlapOne : overlapDefect
      (Finset.univ : Finset (OffCorridorComponent P))
      (fun C => (offCorridorComponentIntervalEdges P C).card)
      ((Finset.univ : Finset (OffCorridorComponent P)).biUnion
        (offCorridorComponentIntervalEdges P)).card = 1) :
    ∃ levels : Finset ℕ,
      levels.card = slack P ∧
      (∀ r < P.length, r ∈ levels ∨ r + 1 ∈ levels) ∧
      (∃! r, r < P.length ∧ r ∈ levels ∧ r + 1 ∈ levels) ∧
      (offCorridorFinset P).image (G.dist w) = levels ∧
      Set.InjOn (G.dist w) (offCorridorFinset P : Set V) := by
  classical
  let components : Finset (OffCorridorComponent P) := Finset.univ
  let size : OffCorridorComponent P → ℕ := fun C =>
    (offCorridorComponentFinset C).card
  let interval : OffCorridorComponent P → Finset ℕ :=
    offCorridorComponentIntervalEdges P
  let span : OffCorridorComponent P → ℕ := fun C => (interval C).card
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
  have hspan : ∀ C ∈ components, span C ≤ size C + 1 := by
    intro C _
    rw [show span C = offCorridorComponentSpan P C by
      simpa [span, interval] using card_offCorridorComponentIntervalEdges P C]
    exact hP.offCorridorComponentSpan_le_card_add_one C
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
  have hunionBound : (components.biUnion interval).card ≤
      ∑ C ∈ components, span C := by
    exact Finset.card_biUnion_le
  obtain ⟨hunitSpan, _hsumSpan⟩ := overlapDefect_structure
    components size span (slack P) (components.biUnion interval).card
    hpositive hmass hspan hunionBound
    (by simpa [components] using hmassZero)
    (by simpa [components, size, span, interval] using hspanZero)
    (by simpa [components, span, interval] using hoverlapOne)
  have hintervalPos : ∀ C, 1 ≤ (interval C).card := by
    intro C
    have h := (hunitSpan C (by simp [components])).2
    simpa [span] using (by omega : 1 ≤ span C)
  let hloExists : ∀ C : OffCorridorComponent P, ∃ l : ℕ,
      interval C = Finset.Ico l (l + span C) := fun C => by
    simpa [interval, span] using
      offCorridorInterval_eq_Ico_card P C (hintervalPos C)
  let lo : OffCorridorComponent P → ℕ := fun C =>
    Classical.choose (hloExists C)
  have hlo : ∀ C, interval C = Finset.Ico (lo C) (lo C + 2) := by
    intro C
    have hspanC := (hunitSpan C (by simp [components])).2
    simpa [lo, hspanC] using Classical.choose_spec (hloExists C)
  have hcardComponents : components.card = slack P := by
    calc
      components.card = ∑ _C ∈ components, 1 := by simp
      _ = ∑ C ∈ components, size C := by
        apply Finset.sum_congr rfl
        intro C hC
        exact (hunitSpan C hC).1.symm
      _ = slack P := hmass
  have hunion : components.biUnion
      (fun C => Finset.Ico (lo C) (lo C + 2)) =
      Finset.range (2 * slack P - 1) := by
    have hfamily : (fun C => Finset.Ico (lo C) (lo C + 2)) = interval := by
      funext C
      exact (hlo C).symm
    rw [← hone]
    rw [hfamily]
    exact hunionActual
  let levels := midpointLevels components lo
  obtain ⟨_hloInj, hlevelsCard, hactive, hhigh⟩ :=
    overlapIntervalProfile components lo (slack P) hs hcardComponents hunion
  have himageComponent : ∀ C,
      (offCorridorComponentFinset C).image (G.dist w) = {lo C + 1} := by
    intro C
    have hC : C ∈ components := by simp [components]
    have hsizeC := (hunitSpan C hC).1
    have hintervalC := hlo C
    have h := IsGeodesic.image_rootDist_singleton_spanTwo
      hconn hP C (lo C) hsizeC hintervalC
    have hinterior : Finset.Ioo (lo C) (lo C + 2) = {lo C + 1} := by
      ext k
      simp only [Finset.mem_Ioo, Finset.mem_singleton]
      omega
    exact h.trans hinterior
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
      have hlevelC : G.dist w x ∈ ({lo C + 1} : Finset ℕ) := by
        rw [← himageComponent C]
        exact Finset.mem_image.mpr ⟨x, hxC, rfl⟩
      have hlevelEq : G.dist w x = lo C + 1 := by simpa using hlevelC
      exact Finset.mem_image.mpr
        ⟨C, by simp [components], hlevelEq.symm⟩
    · intro hk
      obtain ⟨C, _hC, hkEq⟩ := Finset.mem_image.mp hk
      have hkC : k ∈ ({lo C + 1} : Finset ℕ) := by simpa [hkEq]
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
  exact ⟨levels, hlevelsCard, by simpa [levels, hone] using hactive,
    by simpa [levels, hone] using hhigh, himage, hinjective⟩

/-- An even sum has even natural distance. -/
theorem even_natDist_of_even_add {a b : ℕ} (h : Even (a + b)) :
    Even (Nat.dist a b) := by
  rcases h with ⟨q, hq⟩
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab]
    refine ⟨q - a, ?_⟩
    omega
  · rw [Nat.dist_eq_sub_of_le_right hba]
    refine ⟨q - b, ?_⟩
    omega

/-- Equal colors force the two BFS levels from any root to have the same
parity. -/
theorem Coloring.even_natDist_rootLevels_of_eq
    {V : Type*} {G : SimpleGraph V} (hconn : G.Connected)
    (color : G.Coloring Bool) (w : V) {x y : V}
    (hsame : color x = color y) :
    Even (Nat.dist (G.dist w x) (G.dist w y)) := by
  obtain ⟨Qx, hQx⟩ := hconn.exists_walk_length_eq_dist w x
  obtain ⟨Qy, hQy⟩ := hconn.exists_walk_length_eq_dist w y
  let W := Qx.reverse.append Qy
  have hcongr : color x = true ↔ color y = true := by rw [hsame]
  have hEven : Even W.length := (color.even_length_iff_congr W).2 hcongr
  have hlength : W.length = G.dist w x + G.dist w y := by
    simp [W, hQx, hQy]
  rw [hlength] at hEven
  exact even_natDist_of_even_add hEven

/-- BFS level difference never exceeds graph distance. -/
theorem bfsLevel_natDist_le
    {V : Type*} {G : SimpleGraph V} (hconn : G.Connected)
    (w x y : V) :
    Nat.dist (G.dist w x) (G.dist w y) ≤ G.dist x y := by
  have hxy : G.dist w x ≤ G.dist w y + G.dist x y := by
    simpa [SimpleGraph.dist_comm] using hconn.dist_triangle (u := w) (v := y) (w := x)
  have hyx : G.dist w y ≤ G.dist w x + G.dist x y := by
    exact hconn.dist_triangle
  rcases le_total (G.dist w x) (G.dist w y) with hle | hle
  · rw [Nat.dist_eq_sub_of_le hle]
    omega
  · rw [Nat.dist_eq_sub_of_le_right hle]
    omega

/-- Corridor coordinates on a rooted geodesic are their BFS levels. -/
theorem IsGeodesic.rootDist_getVert
    {V : Type*} {G : SimpleGraph V} {w x₀ : V}
    {P : G.Walk w x₀} (hP : IsGeodesic P) {k : ℕ}
    (hk : k ≤ P.length) :
    G.dist w (P.getVert k) = k := by
  have h := hP.dist_getVert_eq_sub (i := 0) (j := k) (by omega) hk
  simpa using h

/-- If two vertices attach to the corridor one step inside their level
interval, the corridor subpath realizes their entire level difference. -/
theorem IsGeodesic.dist_le_levelSub_of_adjacent_corridorAnchors
    {V : Type*} {G : SimpleGraph V} {w x₀ x y : V}
    {P : G.Walk w x₀} (hconn : G.Connected) (hP : IsGeodesic P)
    {a b : ℕ} (hab : a + 2 ≤ b) (hb : b ≤ P.length)
    (hx : G.Adj x (P.getVert (a + 1)))
    (hy : G.Adj (P.getVert (b - 1)) y) :
    G.dist x y ≤ b - a := by
  have ha1 : a + 1 ≤ b - 1 := by omega
  have hb1 : b - 1 ≤ P.length := by omega
  have hpath := hP.dist_getVert_eq_sub ha1 hb1
  have hxDist : G.dist x (P.getVert (a + 1)) = 1 :=
    dist_eq_one_iff_adj.mpr hx
  have hyDist : G.dist (P.getVert (b - 1)) y = 1 :=
    dist_eq_one_iff_adj.mpr hy
  have htri₁ := hconn.dist_triangle (u := x) (v := P.getVert (a + 1)) (w := y)
  have htri₂ := hconn.dist_triangle
    (u := P.getVert (a + 1)) (v := P.getVert (b - 1)) (w := y)
  omega

/-- Oriented routing lemma for a layered graph with one exceptional gap.
All ordinary gaps are complete bipartite between their two level fibers;
at the exceptional gap every vertex has a neighbor across it. -/
theorem IsGeodesic.dist_le_levelSub_of_oneHighLayer
    {V : Type*} {G : SimpleGraph V} {w x₀ x y : V}
    {P : G.Walk w x₀} (hconn : G.Connected) (hP : IsGeodesic P)
    (high : ℕ) (hhigh : high + 1 < P.length)
    (hlow : ∀ {r : ℕ}, r < P.length → r ≠ high →
      ∀ {u v : V}, G.dist w u = r → G.dist w v = r + 1 → G.Adj u v)
    (hforward : ∀ u : V, G.dist w u = high →
      ∃ v : V, G.dist w v = high + 1 ∧ G.Adj u v)
    (hbackward : ∀ v : V, G.dist w v = high + 1 →
      ∃ u : V, G.dist w u = high ∧ G.Adj u v)
    (hxBound : G.dist w x ≤ P.length)
    (hyBound : G.dist w y ≤ P.length)
    (hlt : G.dist w x < G.dist w y)
    (heven : Even (G.dist w y - G.dist w x)) :
    G.dist x y ≤ G.dist w y - G.dist w x := by
  let a := G.dist w x
  let b := G.dist w y
  have hab : a + 2 ≤ b := by
    rcases heven with ⟨q, hq⟩
    omega
  by_cases haHigh : a = high
  · obtain ⟨z, hzLevel, hxz⟩ := hforward x haHigh
    by_cases hbNear : b = high + 2
    · have hzy : G.Adj z y := hlow (r := high + 1) (by omega) (by omega)
          hzLevel (by omega)
      have hxzDist : G.dist x z = 1 := dist_eq_one_iff_adj.mpr hxz
      have hzyDist : G.dist z y = 1 := dist_eq_one_iff_adj.mpr hzy
      have htri := hconn.dist_triangle (u := x) (v := z) (w := y)
      omega
    · have hbFar : high + 1 + 2 ≤ b := by
        rcases heven with ⟨q, hq⟩
        omega
      have hzAnchor : G.Adj z (P.getVert (high + 2)) := by
        apply hlow (r := high + 1) (by omega) (by omega) hzLevel
        exact IsGeodesic.rootDist_getVert hP (by omega)
      have hyAnchor : G.Adj (P.getVert (b - 1)) y := by
        apply hlow (r := b - 1) (by omega) (by omega)
        · exact IsGeodesic.rootDist_getVert hP (by omega)
        · omega
      have hzy := IsGeodesic.dist_le_levelSub_of_adjacent_corridorAnchors
        hconn hP (a := high + 1) (b := b) hbFar hyBound hzAnchor hyAnchor
      have hxzDist : G.dist x z = 1 := dist_eq_one_iff_adj.mpr hxz
      have htri := hconn.dist_triangle (u := x) (v := z) (w := y)
      omega
  · by_cases hbHigh : b - 1 = high
    · have hbEq : b = high + 1 := by omega
      obtain ⟨z, hzLevel, hzy⟩ := hbackward y (by omega)
      by_cases haNear : a = high - 1
      · have hhighPos : 1 ≤ high := by omega
        have hxz : G.Adj x z := by
          apply hlow (r := high - 1) (by omega) (by omega)
          · omega
          · omega
        have hxzDist : G.dist x z = 1 := dist_eq_one_iff_adj.mpr hxz
        have hzyDist : G.dist z y = 1 := dist_eq_one_iff_adj.mpr hzy
        have htri := hconn.dist_triangle (u := x) (v := z) (w := y)
        omega
      · have haFar : a + 2 ≤ high := by
          rcases heven with ⟨q, hq⟩
          omega
        have hxAnchor : G.Adj x (P.getVert (a + 1)) := by
          apply hlow (r := a) (by omega) (by omega)
          · rfl
          · exact IsGeodesic.rootDist_getVert hP (by omega)
        have hzAnchor : G.Adj (P.getVert (high - 1)) z := by
          apply hlow (r := high - 1) (by omega) (by omega)
          · exact IsGeodesic.rootDist_getVert hP (by omega)
          · omega
        have hxz := IsGeodesic.dist_le_levelSub_of_adjacent_corridorAnchors
          hconn hP (a := a) (b := high) haFar (by omega) hxAnchor hzAnchor
        have hzyDist : G.dist z y = 1 := dist_eq_one_iff_adj.mpr hzy
        have htri := hconn.dist_triangle (u := x) (v := z) (w := y)
        omega
    · have hxAnchor : G.Adj x (P.getVert (a + 1)) := by
        apply hlow (r := a) (by omega) haHigh
        · rfl
        · exact IsGeodesic.rootDist_getVert hP (by omega)
      have hyAnchor : G.Adj (P.getVert (b - 1)) y := by
        apply hlow (r := b - 1) (by omega) hbHigh
        · exact IsGeodesic.rootDist_getVert hP (by omega)
        · omega
      exact IsGeodesic.dist_le_levelSub_of_adjacent_corridorAnchors
        hconn hP hab hyBound hxAnchor hyAnchor

/-- Complete alignment theorem for the one-high layer geometry.  Pairs in
one level are assumed to be at distance at most two; legality therefore
forces distinct levels.  Same level parity then invokes the oriented routing
lemma in the appropriate direction. -/
theorem IsGeodesic.levelAligned_of_oneHighLayer
    {V : Type*} {G : SimpleGraph V} {w x₀ x y : V}
    {P : G.Walk w x₀} (hconn : G.Connected) (hP : IsGeodesic P)
    (high : ℕ) (hhigh : high + 1 < P.length)
    (hlow : ∀ {r : ℕ}, r < P.length → r ≠ high →
      ∀ {u v : V}, G.dist w u = r → G.dist w v = r + 1 → G.Adj u v)
    (hforward : ∀ u : V, G.dist w u = high →
      ∃ v : V, G.dist w v = high + 1 ∧ G.Adj u v)
    (hbackward : ∀ v : V, G.dist w v = high + 1 →
      ∃ u : V, G.dist w u = high ∧ G.Adj u v)
    (hsameLayer : ∀ {u v : V}, G.dist w u = G.dist w v → G.dist u v ≤ 2)
    (hxBound : G.dist w x ≤ P.length)
    (hyBound : G.dist w y ≤ P.length)
    (hlevelEven : Even (Nat.dist (G.dist w x) (G.dist w y)))
    (hlegal : 4 ≤ G.dist x y) :
    G.dist x y = Nat.dist (G.dist w x) (G.dist w y) := by
  have hlower := bfsLevel_natDist_le hconn w x y
  rcases lt_trichotomy (G.dist w x) (G.dist w y) with hlt | heq | hgt
  · have hsubEven : Even (G.dist w y - G.dist w x) := by
      simpa [Nat.dist_eq_sub_of_le hlt.le] using hlevelEven
    have hupper := IsGeodesic.dist_le_levelSub_of_oneHighLayer hconn hP high hhigh
      hlow hforward hbackward hxBound hyBound hlt hsubEven
    rw [Nat.dist_eq_sub_of_le hlt.le] at hlower ⊢
    omega
  · have hclose := hsameLayer heq
    omega
  · have hsubEven : Even (G.dist w x - G.dist w y) := by
      simpa [Nat.dist_eq_sub_of_le_right hgt.le] using hlevelEven
    have hupper := IsGeodesic.dist_le_levelSub_of_oneHighLayer hconn hP high hhigh
      hlow hforward hbackward hyBound hxBound hgt hsubEven
    rw [SimpleGraph.dist_comm] at hupper
    rw [Nat.dist_eq_sub_of_le_right hgt.le] at hlower ⊢
    omega

/-- Direct RL landing for a one-high binary layer chain.  This theorem
composes the alignment lemma with the automatic binary-layer profile; every
remaining hypothesis is literal local graph structure or exact layer
cardinality data. -/
theorem totalCost_le_rlBudget_of_oneHighBinaryLayerChain
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀} (m₁ m₂ : I → V)
    (color : G.Coloring Bool) (s d high : ℕ)
    (extra : Fin (d + 1) → ℕ)
    (hconn : G.Connected) (hP : IsGeodesic P) (hPd : P.length = d)
    (hhigh : high + 1 < P.length)
    (hstep : ∀ {u v : V}, G.Adj u v →
      Nat.dist (G.dist w u) (G.dist w v) = 1)
    (hlow : ∀ {r : ℕ}, r < P.length → r ≠ high →
      ∀ {u v : V}, G.dist w u = r → G.dist w v = r + 1 → G.Adj u v)
    (hforward : ∀ u : V, G.dist w u = high →
      ∃ v : V, G.dist w v = high + 1 ∧ G.Adj u v)
    (hbackward : ∀ v : V, G.dist w v = high + 1 →
      ∃ u : V, G.dist w u = high ∧ G.Adj u v)
    (hsameLayer : ∀ {u v : V}, G.dist w u = G.dist w v → G.dist u v ≤ 2)
    (hvertexBound : ∀ v : V, G.dist w v ≤ d)
    (hlayer : ∀ k : Fin (d + 1),
      (levelLayer (G.dist w) k.1).card = extra k + 1)
    (hbinary : ∀ k, extra k ≤ 1)
    (hextra : (∑ k : Fin (d + 1), extra k) ≤ s)
    (hhighBudget :
      (∑ r : Fin d,
        binaryHigh (fun k => if hk : k < d + 1 then extra ⟨k, hk⟩ else 0) r.1) + 1 ≤ s)
    (hRFC : ∀ T : Finset V, w ∉ T →
      (∑ i : I, separationDemand T (m₁ i) (m₂ i)) +
        (if x₀ ∈ T then 1 else 0) ≤ cutSize G T)
    (hlegal : ∀ i, 4 ≤ G.dist (m₁ i) (m₂ i))
    (hsame : ∀ i, color (m₁ i) = color (m₂ i)) :
    (∑ i : I, (G.dist (m₁ i) (m₂ i) + 1) ^ 2) ≤ rlBudget s d := by
  have hroot : G.dist w w = 0 := by simp
  have hstub : G.dist w x₀ = d := by
    rw [← hPd]
    exact hP.symm
  have haligned : ∀ i,
      G.dist (m₁ i) (m₂ i) =
        Nat.dist (G.dist w (m₁ i)) (G.dist w (m₂ i)) := by
    intro i
    apply IsGeodesic.levelAligned_of_oneHighLayer
      hconn hP high hhigh hlow hforward hbackward hsameLayer
      (by rw [hPd]; exact hvertexBound (m₁ i))
      (by rw [hPd]; exact hvertexBound (m₂ i))
      (Coloring.even_natDist_rootLevels_of_eq hconn color w (hsame i))
      (hlegal i)
  exact totalCost_le_rlBudget_of_binaryLayerExtras_levelAligned
    w x₀ m₁ m₂ (G.dist w) s d extra hstep hlayer hbinary hextra
    hhighBudget hroot hstub
    (fun i => hvertexBound (m₁ i)) (fun i => hvertexBound (m₂ i))
    haligned hRFC hlegal

/-- Complete bridge-free closure of the `d = 2s-1` row.  The canonical
defect trichotomy is reduced to the mass and overlap geometries (the span
case is impossible in a bipartite graph), both geometries yield the exact
one-high binary BFS chain, and the automatic layer theorem lands the RL
budget. -/
theorem totalCost_le_rlBudget_of_oneDefect_allNonbridge_sameSide
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀} (m₁ m₂ : I → V)
    (hconn : G.Connected) (color : G.Coloring Bool)
    (hP : IsGeodesic P)
    (hone : P.length = 2 * slack P - 1)
    (hnonbridge : ∀ i < P.length,
      ¬G.IsBridge s(P.getVert i, P.getVert (i + 1)))
    (hRFC : ∀ T : Finset V, w ∉ T →
      (∑ i : I, separationDemand T (m₁ i) (m₂ i)) +
        (if x₀ ∈ T then 1 else 0) ≤ cutSize G T)
    (hs : 5 ≤ slack P)
    (hlegal : ∀ i, 4 ≤ G.dist (m₁ i) (m₂ i))
    (hsame : ∀ i, color (m₁ i) = color (m₂ i)) :
    (∑ i : I, (G.dist (m₁ i) (m₂ i) + 1) ^ 2) ≤
      rlBudget (slack P) (2 * slack P - 1) := by
  classical
  have hsOne : 1 ≤ slack P := by omega
  obtain ⟨components, hall, hcases⟩ :=
    IsGeodesic.canonical_oneDefect_trichotomy
      hP hsOne hone hnonbridge
  let size : OffCorridorComponent P → ℕ := fun C =>
    (offCorridorComponentFinset C).card
  let span : OffCorridorComponent P → ℕ := fun C =>
    (offCorridorComponentIntervalEdges P C).card
  have hpositive : ∀ C ∈ components, 1 ≤ size C := by
    intro C _
    exact offCorridorComponentFinset_card_pos C
  have hmass : ∑ C ∈ components, size C = slack P := by
    have hraw := IsGeodesic.sum_offCorridorComponent_card_eq_slack hP
    convert hraw using 1
    refine Finset.sum_bij (fun C _ => C) ?_ ?_ ?_ ?_
    · intro C _
      simp
    · intro C _ D _ hCD
      exact hCD
    · intro C _
      exact ⟨C, hall C, rfl⟩
    · intro C _
      rfl
  have hspan : ∀ C ∈ components, span C ≤ size C + 1 := by
    intro C _
    rw [show span C = offCorridorComponentSpan P C by
      simpa [span] using card_offCorridorComponentIntervalEdges P C]
    exact hP.offCorridorComponentSpan_le_card_add_one C
  have hcomponents : components =
      (Finset.univ : Finset (OffCorridorComponent P)) :=
    Finset.eq_univ_of_forall hall
  have hfinish : ∀ (levels : Finset ℕ),
      levels.card = slack P →
      (∃! r, r < P.length ∧ r ∈ levels ∧ r + 1 ∈ levels) →
      (offCorridorFinset P).image (G.dist w) = levels →
      Set.InjOn (G.dist w) (offCorridorFinset P : Set V) →
      (∀ C : OffCorridorComponent P, hasOneDefectShape P C) →
      (∑ i : I, (G.dist (m₁ i) (m₂ i) + 1) ^ 2) ≤
        rlBudget (slack P) (2 * slack P - 1) := by
    intro levels hcard hunique himage hinjective hshape
    obtain ⟨high, ⟨hhighLt, hhighE, hhighOneE⟩, hhighUnique⟩ := hunique
    have huniqueFn : ∀ r, r < P.length → r ∈ levels →
        r + 1 ∈ levels → r = high := by
      intro r hr hrE hr1E
      exact hhighUnique r ⟨hr, hrE, hr1E⟩
    have hhighStrict : high + 1 < P.length := by
      have hmem : high + 1 ∈ (offCorridorFinset P).image (G.dist w) := by
        simpa [himage] using hhighOneE
      obtain ⟨x, hxoff, hxlevel⟩ := Finset.mem_image.mp hmem
      have hxlt := IsGeodesic.offVertex_rootDist_lt_length_of_shape
        hconn color hP hshape hxoff
      omega
    obtain ⟨hlow, hforward, hbackward, hsameLayer⟩ :=
      IsGeodesic.localOneHighGeometry_of_componentShapes
        hconn color hP levels high
        ⟨hhighLt, hhighE, hhighOneE⟩ huniqueFn
        himage hinjective hshape
    have hvertexBound : ∀ v : V, G.dist w v ≤ P.length :=
      IsGeodesic.rootDist_le_length_of_componentShapes
        hconn color hP hshape
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
    let extra : Fin (P.length + 1) → ℕ := levelIndicator levels
    have hlayer : ∀ k : Fin (P.length + 1),
        (levelLayer (G.dist w) k.1).card = extra k + 1 := by
      intro k
      have hk := IsGeodesic.levelLayer_card_eq_one_add_indicator
        hP levels hinjective himage (k := k.1) (by omega)
      simpa [extra, levelIndicator, Nat.add_comm] using hk
    have hsub : levels ⊆ Finset.range (P.length + 1) := by
      intro k hk
      have hkImage : k ∈ (offCorridorFinset P).image (G.dist w) := by
        simpa [himage] using hk
      obtain ⟨x, hxoff, hxlevel⟩ := Finset.mem_image.mp hkImage
      have hxlt := IsGeodesic.offVertex_rootDist_lt_length_of_shape
        hconn color hP hshape hxoff
      exact Finset.mem_range.mpr (by omega)
    obtain ⟨hbinary, hextraEq, hhighEq⟩ :=
      indicatorProfile_counts levels P.length (slack P)
        hsub hcard ⟨high, ⟨hhighLt, hhighE, hhighOneE⟩, hhighUnique⟩
    have hextra : (∑ k : Fin (P.length + 1), extra k) ≤ slack P := by
      have heq : (∑ k : Fin (P.length + 1), extra k) = slack P := by
        simpa [extra] using hextraEq
      omega
    have hhighBudget :
        (∑ r : Fin P.length,
          binaryHigh
            (fun k => if hk : k < P.length + 1 then extra ⟨k, hk⟩ else 0)
            r.1) + 1 ≤ slack P := by
      have heq :
          (∑ r : Fin P.length,
            binaryHigh
              (fun k => if hk : k < P.length + 1 then
                extra ⟨k, hk⟩ else 0) r.1) = 1 := by
        have hext :
            (fun k => if hk : k < P.length + 1 then
              extra ⟨k, hk⟩ else 0) =
              extendedLevelIndicator levels P.length := by
          funext k
          by_cases hk : k < P.length + 1
          · simp [extendedLevelIndicator, extra, hk, levelIndicator]
          · simp [extendedLevelIndicator, hk]
        rw [hext]
        exact hhighEq
      omega
    have hresult := totalCost_le_rlBudget_of_oneHighBinaryLayerChain
      m₁ m₂ color (slack P) P.length high extra
      hconn hP rfl hhighStrict hstep hlow hforward hbackward hsameLayer
      hvertexBound hlayer hbinary hextra hhighBudget hRFC hlegal hsame
    simpa [hone] using hresult
  rcases hcases with hmassCase | hspanCase | hoverlapCase
  · have hshape := componentShapes_of_massDefect P components hall
      (by simpa [size] using hpositive) (by simpa [size] using hmass)
      (by simpa [size, span] using hspan)
      hmassCase.1 hmassCase.2.1
    have hmassOne : massDefect
        (Finset.univ : Finset (OffCorridorComponent P)) (slack P) = 1 := by
      simpa only [← hcomponents] using hmassCase.1
    have hspanZero : spanDefect
        (Finset.univ : Finset (OffCorridorComponent P))
        (fun C => (offCorridorComponentFinset C).card)
        (fun C => (offCorridorComponentIntervalEdges P C).card) = 0 := by
      simpa only [← hcomponents] using hmassCase.2.1
    have hoverlapZero : overlapDefect
        (Finset.univ : Finset (OffCorridorComponent P))
        (fun C => (offCorridorComponentIntervalEdges P C).card)
        ((Finset.univ : Finset (OffCorridorComponent P)).biUnion
          (offCorridorComponentIntervalEdges P)).card = 0 := by
      simpa only [← hcomponents] using hmassCase.2.2
    obtain ⟨levels, hcard, _hactive, hunique, himage, hinjective⟩ :=
      IsGeodesic.massDefect_rootLevelProfile
        hconn color hP hsOne hone hnonbridge
        hmassOne hspanZero hoverlapZero
    exact hfinish levels hcard hunique himage hinjective hshape
  · exact (canonical_spanDefect_case_false color P components
      (by simpa [size] using hpositive) (by simpa [size] using hmass)
      (by simpa [size, span] using hspan)
      hspanCase.1 hspanCase.2.1).elim
  · have hshape := componentShapes_of_overlapDefect P components hall
      (by simpa [size] using hpositive) (by simpa [size] using hmass)
      (by simpa [size, span] using hspan)
      hoverlapCase.1 hoverlapCase.2.1
    have hmassZero : massDefect
        (Finset.univ : Finset (OffCorridorComponent P)) (slack P) = 0 := by
      simpa only [← hcomponents] using hoverlapCase.1
    have hspanZero : spanDefect
        (Finset.univ : Finset (OffCorridorComponent P))
        (fun C => (offCorridorComponentFinset C).card)
        (fun C => (offCorridorComponentIntervalEdges P C).card) = 0 := by
      simpa only [← hcomponents] using hoverlapCase.2.1
    have hoverlapOne : overlapDefect
        (Finset.univ : Finset (OffCorridorComponent P))
        (fun C => (offCorridorComponentIntervalEdges P C).card)
        ((Finset.univ : Finset (OffCorridorComponent P)).biUnion
          (offCorridorComponentIntervalEdges P)).card = 1 := by
      simpa only [← hcomponents] using hoverlapCase.2.2
    obtain ⟨levels, hcard, _hactive, hunique, himage, hinjective⟩ :=
      IsGeodesic.overlapDefect_rootLevelProfile
        hconn hP hsOne hone hnonbridge
        hmassZero hspanZero hoverlapOne
    exact hfinish levels hcard hunique himage hinjective hshape

#print axioms bfsLevel_natDist_le
#print axioms IsGeodesic.rootDist_getVert
#print axioms IsGeodesic.dist_le_levelSub_of_adjacent_corridorAnchors
#print axioms IsGeodesic.dist_le_levelSub_of_oneHighLayer
#print axioms IsGeodesic.levelAligned_of_oneHighLayer
#print axioms Coloring.even_natDist_rootLevels_of_eq
#print axioms totalCost_le_rlBudget_of_oneHighBinaryLayerChain
#print axioms totalCost_le_rlBudget_of_oneDefect_allNonbridge_sameSide

end Erdos23GapGBOneDefectAlignment
