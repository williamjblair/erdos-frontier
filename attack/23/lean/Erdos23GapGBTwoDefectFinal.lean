/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair, OpenAI Codex
-/
import ErdosProblems.Erdos23GapGBTwoDefectAlignment

/-!
# Erdős 23 G-B: final graph constructors on the two-defect boundary

This module closes the four canonical graph shapes left after the exact
`d = 2s-2` deficit classification.
-/

namespace Erdos23GapGBTwoDefectFinal

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
open Erdos23GapGBTwoDefectAlignment

/-- A positive finite level set of size `s` that meets every one of the `d`
consecutive level gaps at the two-defect row has at most two adjacent pairs.
The endpoint level `d` is allowed, which is needed for the mass/span tip. -/
theorem activeLevelSet_high_card_le_two
    (E : Finset ℕ) (s d : ℕ)
    (hd : d = 2 * s - 2)
    (hsub : E ⊆ Finset.range (d + 1))
    (hpos : ∀ k ∈ E, 1 ≤ k)
    (hcard : E.card = s)
    (hactive : ∀ r < d, r ∈ E ∨ r + 1 ∈ E) :
    ((Finset.range d).filter fun r => r ∈ E ∧ r + 1 ∈ E).card ≤ 2 := by
  classical
  let predE := E.image Nat.pred
  have hpredSub : predE ⊆ Finset.range d := by
    intro r hr
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hr
    have heRange := Finset.mem_range.mp (hsub he)
    have hePos := hpos e he
    have hsucc : Nat.pred e + 1 = e := Nat.succ_pred_eq_of_pos (by omega)
    exact Finset.mem_range.mpr (by omega)
  have hrangeSub : Finset.range d ⊆ E ∪ predE := by
    intro r hr
    have hrlt := Finset.mem_range.mp hr
    rcases hactive r hrlt with hrE | hr1E
    · exact Finset.mem_union_left predE hrE
    · apply Finset.mem_union_right E
      exact Finset.mem_image.mpr ⟨r + 1, hr1E, by simp⟩
  have hpredInj : Set.InjOn Nat.pred (E : Set ℕ) := by
    intro a ha b hb hab
    have haPos := hpos a ha
    have hbPos := hpos b hb
    have haSucc : Nat.pred a + 1 = a := Nat.succ_pred_eq_of_pos (by omega)
    have hbSucc : Nat.pred b + 1 = b := Nat.succ_pred_eq_of_pos (by omega)
    omega
  have hcardPred : predE.card = E.card := by
    exact Finset.card_image_iff.mpr hpredInj
  have hcardUnion := Finset.card_union_add_card_inter E predE
  have hrangeCardLe : d ≤ (E ∪ predE).card := by
    simpa using Finset.card_le_card hrangeSub
  have hinterLe : (E ∩ predE).card ≤ 2 := by
    rw [hcardPred, hcard] at hcardUnion
    omega
  have hfilterEq :
      (Finset.range d).filter (fun r => r ∈ E ∧ r + 1 ∈ E) =
        E ∩ predE := by
    ext r
    constructor
    · intro hr
      have hrData := Finset.mem_filter.mp hr
      exact Finset.mem_inter.mpr
        ⟨hrData.2.1,
          Finset.mem_image.mpr ⟨r + 1, hrData.2.2, by simp⟩⟩
    · intro hr
      have hrData := Finset.mem_inter.mp hr
      obtain ⟨e, heE, hePred⟩ := Finset.mem_image.mp hrData.2
      have hePos := hpos e heE
      have heSucc : Nat.pred e + 1 = e := Nat.succ_pred_eq_of_pos (by omega)
      have her : e = r + 1 := by omega
      have hrRange := hpredSub hrData.2
      exact Finset.mem_filter.mpr
        ⟨hrRange, hrData.1, by simpa [her] using heE⟩
  rw [hfilterEq]
  exact hinterLe

/-- If both endpoints have the ordinary corridor anchors immediately below
and above their rooted levels, every legal same-side pair is level aligned. -/
theorem IsGeodesic.levelAligned_of_twoSidedAnchors
    {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ x y : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P)
    (hxNext : G.dist w x < P.length →
      G.Adj x (P.getVert (G.dist w x + 1)))
    (hxPrev : 0 < G.dist w x →
      G.Adj (P.getVert (G.dist w x - 1)) x)
    (hyNext : G.dist w y < P.length →
      G.Adj y (P.getVert (G.dist w y + 1)))
    (hyPrev : 0 < G.dist w y →
      G.Adj (P.getVert (G.dist w y - 1)) y)
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
    · have hxAnchor := hxPrev (by omega)
      have hyAnchor := hyPrev (by omega)
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
    have hupper := IsGeodesic.dist_le_levelSub_of_adjacent_corridorAnchors
      hconn hP hgap hyBound (hxNext (by omega)) (hyPrev (by omega))
    rw [Nat.dist_eq_sub_of_le hlt.le] at hlower ⊢
    omega
  · have hclose := hsame heq
    omega
  · have heven : Even (G.dist w x - G.dist w y) := by
      simpa [Nat.dist_eq_sub_of_le_right hgt.le] using hlevelEven
    obtain ⟨q, hq⟩ := heven
    have hgap : G.dist w y + 2 ≤ G.dist w x := by omega
    have hupper := IsGeodesic.dist_le_levelSub_of_adjacent_corridorAnchors
      hconn hP hgap hxBound (hyNext (by omega)) (hxPrev (by omega))
    rw [SimpleGraph.dist_comm] at hupper
    rw [Nat.dist_eq_sub_of_le_right hgt.le] at hlower ⊢
    omega

set_option maxHeartbeats 800000 in
/-- The local shortest-path extraction below traverses component-complement
quotients, so this isolated theorem needs a larger elaboration budget. -/
theorem IsGeodesic.pair_spanTwo_geometry
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (color : G.Coloring Bool) (hP : IsGeodesic P)
    (C : OffCorridorComponent P) (l : ℕ)
    (hsize : (offCorridorComponentFinset C).card = 2)
    (hinterval : offCorridorComponentIntervalEdges P C =
      Finset.Ico l (l + 2)) :
    ∃ anchor tip : V,
      offCorridorComponentFinset C = {anchor, tip} ∧
      anchor ≠ tip ∧ G.Adj anchor tip ∧
      G.Adj anchor (P.getVert l) ∧
      G.Adj anchor (P.getVert (l + 2)) ∧
      G.dist w anchor = l + 1 ∧ G.dist w tip = l + 2 := by
  classical
  obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp hsize
  have hAdjAB : G.Adj a b :=
    offCorridorComponent_adj_of_finset_eq_pair C hab hset
  obtain ⟨hleft, hright, hbounds⟩ :=
    attachment_extrema_of_interval_eq_length P C l 2 (by omega) hinterval
  obtain ⟨hlLength, cL, hcL, hAdjL⟩ :=
    (mem_offCorridorAttachmentIndices P C l).1 hleft
  obtain ⟨hrLength, cR, hcR, hAdjR⟩ :=
    (mem_offCorridorAttachmentIndices P C (l + 2)).1 hright
  have hcEq : cL = cR := by
    by_contra hne
    have hcLcases : cL = a ∨ cL = b := by simpa [hset] using hcL
    have hcRcases : cR = a ∨ cR = b := by simpa [hset] using hcR
    have hAdjLR : G.Adj cL cR := by
      rcases hcLcases with rfl | rfl <;> rcases hcRcases with rfl | rfl
      · exact (hne rfl).elim
      · exact hAdjAB
      · exact hAdjAB.symm
      · exact (hne rfl).elim
    have hp₁ := color.valid (P.adj_getVert_succ (i := l) (by omega))
    have hp₂ := color.valid (P.adj_getVert_succ (i := l + 1) (by omega))
    have hcl := color.valid hAdjL
    have hcr := color.valid hAdjR
    have hlr := color.valid hAdjLR
    cases h0 : color (P.getVert l) <;>
      cases h1 : color (P.getVert (l + 1)) <;>
      cases h2 : color (P.getVert (l + 2)) <;>
      cases hL : color cL <;>
      cases hR : color cR <;>
      simp_all
  subst cR
  have hcLcases : cL = a ∨ cL = b := by simpa [hset] using hcL
  obtain ⟨tip, hcomponent, hne, hAdjAT⟩ :
      ∃ tip : V, offCorridorComponentFinset C = {cL, tip} ∧
        cL ≠ tip ∧ G.Adj cL tip := by
    rcases hcLcases with hca | hcb
    · subst cL
      exact ⟨b, hset, hab, hAdjAB⟩
    · subst cL
      exact ⟨a, by simpa [Finset.pair_comm] using hset,
        hab.symm, hAdjAB.symm⟩
  have hleftLevel : G.dist w (P.getVert l) = l := by
    simpa using hP.dist_getVert_eq_sub (i := 0) (j := l) (by omega) hlLength
  have hrightLevel : G.dist w (P.getVert (l + 2)) = l + 2 := by
    simpa using hP.dist_getVert_eq_sub (i := 0) (j := l + 2)
      (by omega) hrLength
  have hAdjLDist : G.dist (P.getVert l) cL = 1 :=
    dist_eq_one_iff_adj.mpr hAdjL.symm
  have hAdjRDist : G.dist cL (P.getVert (l + 2)) = 1 :=
    dist_eq_one_iff_adj.mpr hAdjR
  have hupperA := hconn.dist_triangle (u := w) (v := P.getVert l) (w := cL)
  have hlowerA := hconn.dist_triangle
    (u := w) (v := cL) (w := P.getVert (l + 2))
  have hlevelA : G.dist w cL = l + 1 := by omega
  have htC : tip ∈ offCorridorComponentFinset C := by simp [hcomponent]
  have htComp : tip ∈ C := (mem_offCorridorComponentFinset C).1 htC
  obtain ⟨htOffSet, htCompEq⟩ := ComponentCompl.mem_supp_iff.mp htComp
  have htNot : tip ∉ P.support := by simpa [supportFinset] using htOffSet
  have hneighborLower : ∀ y : V, G.Adj tip y → l + 1 ≤ G.dist w y := by
    intro y hty
    by_cases hySupport : y ∈ P.support
    · let j := P.support.idxOf y
      have hjLength : j ≤ P.length := support_idxOf_le_length P hySupport
      have hjGet : P.getVert j = y := P.getVert_support_idxOf hySupport
      have hjAttach : j ∈ offCorridorAttachmentIndices P C := by
        exact (mem_offCorridorAttachmentIndices P C j).2
          ⟨hjLength, tip, htC, by simpa [hjGet] using hty⟩
      have hjBounds := hbounds j hjAttach
      have hjLevel : G.dist w y = j := by
        rw [← hjGet]
        exact IsGeodesic.rootDist_getVert hP hjLength
      have hjNe : j ≠ l := by
        intro hjEq
        have htipLeft : G.Adj tip (P.getVert l) := by
          have h := hty
          rw [← hjGet, hjEq] at h
          exact h
        have hat := color.valid hAdjAT
        have hal := color.valid hAdjL
        have htl := color.valid htipLeft
        cases ht : color tip <;>
          cases ha : color cL <;>
          cases hp : color (P.getVert l) <;>
          simp_all
      omega
    · have hcompEq := offCorridorComponentOf_eq_of_adj P htNot hySupport hty
      have htOwn : offCorridorComponentOf P tip htNot = C := by
        simpa [offCorridorComponentOf, supportFinset] using htCompEq
      have hyOwn : y ∈ offCorridorComponentFinset
          (offCorridorComponentOf P y hySupport) :=
        mem_offCorridorComponentOf P hySupport
      have hyC : y ∈ offCorridorComponentFinset C := by
        simpa [← htOwn, hcompEq] using hyOwn
      have hyCases : y = cL ∨ y = tip := by simpa [hcomponent] using hyC
      rcases hyCases with hy | hy
      · subst y
        omega
      · subst y
        exact (G.loopless.irrefl tip hty).elim
  have htUpper : G.dist w tip ≤ l + 2 := by
    have hATDist : G.dist cL tip = 1 := dist_eq_one_iff_adj.mpr hAdjAT
    have htri := hconn.dist_triangle (u := w) (v := cL) (w := tip)
    omega
  have hwSupport : w ∈ P.support := by simpa using P.getVert_mem_support 0
  have htw : tip ≠ w := by
    intro h
    subst tip
    exact htNot hwSupport
  obtain ⟨Q, hQ⟩ := hconn.exists_walk_length_eq_dist w tip
  have hQnotNil : ¬ Q.Nil := by
    intro hnil
    have hwt : w = tip := hnil.eq
    exact htw hwt.symm
  have hpenAdj : G.Adj tip Q.penultimate := (Q.adj_penultimate hQnotNil).symm
  have hpenLower := hneighborLower Q.penultimate hpenAdj
  have hdrop : G.dist w Q.penultimate ≤ Q.dropLast.length := dist_le Q.dropLast
  have hlen := Q.length_dropLast_add_one hQnotNil
  have htLower : l + 2 ≤ G.dist w tip := by omega
  have htLevel : G.dist w tip = l + 2 := by omega
  exact ⟨cL, tip, hcomponent, hne, hAdjAT, hAdjL, hAdjR,
    hlevelA, htLevel⟩

/-- If every off-corridor component is a saturated singleton of span two,
every vertex has the corridor anchors immediately below and above its rooted
level whenever those anchors are in range. -/
theorem IsGeodesic.allSingletonSpanTwo_twoSidedAnchors
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ v : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P)
    (hshape : ∀ C : OffCorridorComponent P,
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2) :
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
    obtain ⟨hsize, hspan⟩ := hshape C
    obtain ⟨l, hinterval⟩ :=
      offCorridorInterval_eq_Ico_of_card_eq_two P C hspan
    obtain ⟨c, hset, hlevel, hleft, hright⟩ :=
      IsGeodesic.singleton_spanTwo_geometry
        hconn hP C l hsize hinterval
    have hvc : v = c := by simpa [hset] using hvC
    subst v
    constructor
    · intro _
      simpa [hlevel] using hright
    · intro _
      simpa [hlevel] using hleft.symm

/-- Off-corridor level fibers decompose exactly as the disjoint union of
the corresponding fibers inside the canonical off-corridor components. -/
theorem offLevelFiber_card_eq_sum_componentLevelFiber_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ : V} {P : G.Walk w x₀}
    [Fintype (OffCorridorComponent P)]
    (level : V → ℕ) (k : ℕ) :
    (offLevelFiber P level k).card =
      ∑ C : OffCorridorComponent P,
        ((offCorridorComponentFinset C).filter
          fun v => level v = k).card := by
  classical
  let family : OffCorridorComponent P → Finset V := fun C =>
    (offCorridorComponentFinset C).filter fun v => level v = k
  have hdisjoint :
      (↑(Finset.univ : Finset (OffCorridorComponent P)) :
        Set (OffCorridorComponent P)).PairwiseDisjoint family := by
    intro C _ D _ hCD
    change Disjoint (family C) (family D)
    rw [Finset.disjoint_left]
    intro x hxC hxD
    have hxC' : x ∈ C := (mem_offCorridorComponentFinset C).1
      (Finset.mem_filter.mp hxC).1
    have hxD' : x ∈ D := (mem_offCorridorComponentFinset D).1
      (Finset.mem_filter.mp hxD).1
    obtain ⟨_hxOffC, hxEqC⟩ := ComponentCompl.mem_supp_iff.mp hxC'
    obtain ⟨_hxOffD, hxEqD⟩ := ComponentCompl.mem_supp_iff.mp hxD'
    have hEq : C = D := by rw [← hxEqC, ← hxEqD]
    exact hCD hEq
  have hunion :
      (Finset.univ : Finset (OffCorridorComponent P)).biUnion family =
        offLevelFiber P level k := by
    ext x
    constructor
    · intro hx
      obtain ⟨C, _hC, hxC⟩ := Finset.mem_biUnion.mp hx
      have hxData := Finset.mem_filter.mp hxC
      exact Finset.mem_filter.mpr
        ⟨mem_offCorridorFinset_of_mem_componentFinset hxData.1,
          hxData.2⟩
    · intro hx
      have hxData := Finset.mem_filter.mp hx
      have hxNot : x ∉ P.support := by
        have hxsupport := (Finset.mem_sdiff.mp hxData.1).2
        simpa [supportFinset] using hxsupport
      let C := offCorridorComponentOf P x hxNot
      have hxC : x ∈ offCorridorComponentFinset C :=
        mem_offCorridorComponentOf P hxNot
      exact Finset.mem_biUnion.mpr
        ⟨C, by simp, Finset.mem_filter.mpr ⟨hxC, hxData.2⟩⟩
  rw [← hunion, Finset.card_biUnion hdisjoint]

set_option maxHeartbeats 2000000

/-- Named component geometry and the unique overlap coordinate for the
mixed mass-overlap branch.  The unique double coordinate is not the middle
edge of the span-three pair. -/
theorem IsGeodesic.massOverlap_namedProfile
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    [Fintype (OffCorridorComponent P)]
    (hconn : G.Connected) (color : G.Coloring Bool) (hP : IsGeodesic P)
    (hnonbridge : ∀ i < P.length,
      ¬G.IsBridge s(P.getVert i, P.getVert (i + 1)))
    (hmixed :
      let components := (Finset.univ : Finset (OffCorridorComponent P))
      let size : OffCorridorComponent P → ℕ := fun C =>
        (offCorridorComponentFinset C).card
      let span : OffCorridorComponent P → ℕ := fun C =>
        (offCorridorComponentIntervalEdges P C).card
      let unionCard :=
        (components.biUnion (offCorridorComponentIntervalEdges P)).card
      MassOverlapShape components size span (slack P) unionCard) :
    ∃ Cstar : OffCorridorComponent P, ∃ a : ℕ, ∃ cL cR : V, ∃ j : ℕ,
      offCorridorComponentFinset Cstar = {cL, cR} ∧
      cL ≠ cR ∧ G.Adj cL cR ∧
      G.Adj cL (P.getVert a) ∧
      G.Adj cR (P.getVert (a + 3)) ∧
      G.dist w cL = a + 1 ∧ G.dist w cR = a + 2 ∧
      offCorridorComponentIntervalEdges P Cstar = Finset.Ico a (a + 3) ∧
      (∀ C : OffCorridorComponent P, C ≠ Cstar →
        (offCorridorComponentFinset C).card = 1 ∧
        (offCorridorComponentIntervalEdges P C).card = 2) ∧
      j ∈ Finset.range P.length ∧
      coverMultiplicity
          (Finset.univ : Finset (OffCorridorComponent P))
          (offCorridorComponentIntervalEdges P) j = 2 ∧
      (∀ r ∈ Finset.range P.length, r ≠ j →
        coverMultiplicity
            (Finset.univ : Finset (OffCorridorComponent P))
            (offCorridorComponentIntervalEdges P) r = 1) ∧
      j ≠ a + 1 := by
  classical
  let components : Finset (OffCorridorComponent P) := Finset.univ
  let size : OffCorridorComponent P → ℕ := fun C =>
    (offCorridorComponentFinset C).card
  let interval : OffCorridorComponent P → Finset ℕ :=
    offCorridorComponentIntervalEdges P
  let span : OffCorridorComponent P → ℕ := fun C => (interval C).card
  let unionCard := (components.biUnion interval).card
  change MassOverlapShape components size span (slack P) unionCard at hmixed
  rcases hmixed with
    ⟨hmassOne, hspanZero, hoverlapOne, Cstar, _hCstar,
      hstarSize, hstarSpan, hothersRaw⟩
  have hothers : ∀ C : OffCorridorComponent P, C ≠ Cstar →
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2 := by
    intro C hC
    have h := hothersRaw C (by simp [components]) hC
    simpa [size, span, interval] using h
  have hstarCard :
      (offCorridorComponentIntervalEdges P Cstar).card = 3 := by
    simpa [span, interval] using hstarSpan
  obtain ⟨a, hstarInterval⟩ :=
    offCorridorInterval_eq_Ico_card P Cstar (by omega)
  have hstarInterval' : offCorridorComponentIntervalEdges P Cstar =
      Finset.Ico a (a + 3) := by
    simpa [hstarCard] using hstarInterval
  obtain ⟨cL, cR, hstar, hne, hLR, hleft, hright,
      hlevelL, hlevelR⟩ :=
    IsGeodesic.pair_spanThree_geometry
      hconn color hP Cstar a hstarSize hstarInterval'
  have hunion : components.biUnion interval = Finset.range P.length := by
    have hraw :=
      IsGeodesic.biUnion_offCorridorIntervals_eq_range hP hnonbridge
    convert hraw using 1
    apply Finset.Subset.antisymm
    · intro r hr
      obtain ⟨C, _hC, hrC⟩ := Finset.mem_biUnion.mp hr
      exact Finset.mem_biUnion.mpr ⟨C, by simp [components], by simpa [interval] using hrC⟩
    · intro r hr
      obtain ⟨C, _hC, hrC⟩ := Finset.mem_biUnion.mp hr
      exact Finset.mem_biUnion.mpr ⟨C, by simp [components], by simpa [interval] using hrC⟩
  have hunionCard : unionCard = P.length := by
    dsimp [unionCard]
    rw [hunion]
    simp
  have hmixedLength : MassOverlapShape components
      (fun C => (offCorridorComponentFinset C).card)
      (fun C => (offCorridorComponentIntervalEdges P C).card)
      (slack P) P.length := by
    rw [← hunionCard]
    simpa [size, span, interval] using
      (show MassOverlapShape components size span (slack P) unionCard from
        ⟨hmassOne, hspanZero, hoverlapOne, Cstar, by simp [components],
          hstarSize, hstarSpan, hothersRaw⟩)
  obtain ⟨j, ⟨hjRange, hjTwo, hbase⟩, _hjUnique⟩ :=
    canonical_massOverlap_unique_double_coordinate
      P components hunion hmixedLength
  have hjne : j ≠ a + 1 := by
    intro hja
    have hmidStar : a + 1 ∈
        offCorridorComponentIntervalEdges P Cstar := by
      rw [hstarInterval']
      simp
    have hextraComponent : ∃ C : OffCorridorComponent P,
        C ≠ Cstar ∧ a + 1 ∈ offCorridorComponentIntervalEdges P C := by
      by_contra hnone
      push_neg at hnone
      have hfilter :
          (components.filter fun C =>
            a + 1 ∈ offCorridorComponentIntervalEdges P C) = {Cstar} := by
        ext C
        constructor
        · intro hC
          have hCdata := Finset.mem_filter.mp hC
          have hEq : C = Cstar := by
            by_contra hneC
            exact hnone C hneC hCdata.2
          simpa [hEq]
        · intro hC
          have hEq : C = Cstar := by simpa using hC
          subst C
          exact Finset.mem_filter.mpr ⟨by simp [components], hmidStar⟩
      have htwoFilter :
          (components.filter fun C =>
            a + 1 ∈ offCorridorComponentIntervalEdges P C).card = 2 := by
        rw [← coverMultiplicity_eq_card_filter]
        simpa [components, interval, hja] using hjTwo
      rw [hfilter] at htwoFilter
      simp at htwoFilter
    obtain ⟨C, hCne, hmidC⟩ := hextraComponent
    obtain ⟨l, hCInterval⟩ :=
      offCorridorInterval_eq_Ico_of_card_eq_two P C (hothers C hCne).2
    have hlBounds : l ≤ a + 1 ∧ a + 1 < l + 2 := by
      simpa [hCInterval] using hmidC
    have hlCases : l = a ∨ l = a + 1 := by omega
    have htwoAt (r : ℕ)
        (hrStar : r ∈ offCorridorComponentIntervalEdges P Cstar)
        (hrC : r ∈ offCorridorComponentIntervalEdges P C) :
        2 ≤ coverMultiplicity components interval r := by
      have hpairSub : ({Cstar, C} : Finset (OffCorridorComponent P)) ⊆
          components.filter (fun D => r ∈ interval D) := by
        intro D hD
        have hcases : D = Cstar ∨ D = C := by simpa using hD
        rcases hcases with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨by simp [components], by simpa [interval] using hrStar⟩
        · exact Finset.mem_filter.mpr ⟨by simp [components], by simpa [interval] using hrC⟩
      have hpairCard : ({Cstar, C} : Finset (OffCorridorComponent P)).card = 2 := by
        simp [hCne.symm]
      rw [coverMultiplicity_eq_card_filter]
      rw [← hpairCard]
      exact Finset.card_le_card hpairSub
    rcases hlCases with hlEq | hlEq
    · have haStar : a ∈ offCorridorComponentIntervalEdges P Cstar := by
        rw [hstarInterval']
        simp
      have haC : a ∈ offCorridorComponentIntervalEdges P C := by
        rw [hCInterval, hlEq]
        simp
      have haRange := offCorridorComponentIntervalEdges_subset_range P Cstar haStar
      have haBase := hbase a haRange (by omega)
      have haTwo := htwoAt a haStar haC
      have haBase' : coverMultiplicity components interval a = 1 := by
        simpa [components, interval] using haBase
      omega
    · have haTwoStar : a + 2 ∈
          offCorridorComponentIntervalEdges P Cstar := by
        rw [hstarInterval']
        simp
      have haTwoC : a + 2 ∈ offCorridorComponentIntervalEdges P C := by
        rw [hCInterval, hlEq]
        simp
      have haTwoRange :=
        offCorridorComponentIntervalEdges_subset_range P Cstar haTwoStar
      have haTwoBase := hbase (a + 2) haTwoRange (by omega)
      have haTwoMultiplicity := htwoAt (a + 2) haTwoStar haTwoC
      have haTwoBase' :
          coverMultiplicity components interval (a + 2) = 1 := by
        simpa [components, interval] using haTwoBase
      omega
  exact ⟨Cstar, a, cL, cR, j, hstar, hne, hLR, hleft, hright,
    hlevelL, hlevelR, hstarInterval', hothers, hjRange,
    by simpa [components, interval] using hjTwo,
    by
      intro r hr hrj
      simpa [components, interval] using hbase r hr hrj,
    hjne⟩

set_option maxHeartbeats 800000
set_option maxRecDepth 10000

set_option maxHeartbeats 1000000

private theorem IsGeodesic.massOverlap_vertex_adjacent_interval_coordinates
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ cL cR v : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P)
    (Cstar C : OffCorridorComponent P) (a : ℕ)
    (hstar : offCorridorComponentFinset Cstar = {cL, cR})
    (hlevelL : G.dist w cL = a + 1)
    (hlevelR : G.dist w cR = a + 2)
    (hstarInterval : offCorridorComponentIntervalEdges P Cstar =
      Finset.Ico a (a + 3))
    (hothers : ∀ D : OffCorridorComponent P, D ≠ Cstar →
      (offCorridorComponentFinset D).card = 1 ∧
      (offCorridorComponentIntervalEdges P D).card = 2)
    (hvC : v ∈ offCorridorComponentFinset C) :
    0 < G.dist w v ∧
      G.dist w v - 1 ∈ offCorridorComponentIntervalEdges P C ∧
      G.dist w v ∈ offCorridorComponentIntervalEdges P C := by
  classical
  by_cases hC : C = Cstar
  · subst C
    have hvCases : v = cL ∨ v = cR := by
      simpa [hstar] using hvC
    rcases hvCases with rfl | rfl
    · refine ⟨by omega, ?_, ?_⟩
      · rw [hstarInterval]
        simp only [Finset.mem_Ico]
        rw [hlevelL]
        omega
      · rw [hstarInterval]
        simp only [Finset.mem_Ico]
        rw [hlevelL]
        omega
    · refine ⟨by omega, ?_, ?_⟩
      · rw [hstarInterval]
        simp only [Finset.mem_Ico]
        rw [hlevelR]
        omega
      · rw [hstarInterval]
        simp only [Finset.mem_Ico]
        rw [hlevelR]
        omega
  · obtain ⟨hsize, hspan⟩ := hothers C hC
    obtain ⟨l, hinterval⟩ :=
      offCorridorInterval_eq_Ico_of_card_eq_two P C hspan
    obtain ⟨c, hset, hlevel, _hleft, _hright⟩ :=
      IsGeodesic.singleton_spanTwo_geometry
        hconn hP C l hsize hinterval
    have hvc : v = c := by simpa [hset] using hvC
    subst v
    refine ⟨by omega, ?_, ?_⟩
    · rw [hinterval]
      simp only [Finset.mem_Ico]
      rw [hlevel]
      omega
    · rw [hinterval]
      simp only [Finset.mem_Ico]
      rw [hlevel]
      omega

/-- In the named mixed mass-overlap profile, uniqueness of the one
double-covered gap forces the rooted distance to be injective on all
off-corridor vertices.  Distinct vertices at one level would make their
distinct components share both adjacent gap coordinates. -/
theorem IsGeodesic.massOverlap_rootDist_injective_of_uniqueDouble
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ cL cR : V} {P : G.Walk w x₀}
    [Fintype (OffCorridorComponent P)]
    (hconn : G.Connected) (hP : IsGeodesic P)
    (Cstar : OffCorridorComponent P) (a j : ℕ)
    (hstar : offCorridorComponentFinset Cstar = {cL, cR})
    (hlevelL : G.dist w cL = a + 1)
    (hlevelR : G.dist w cR = a + 2)
    (hstarInterval : offCorridorComponentIntervalEdges P Cstar =
      Finset.Ico a (a + 3))
    (hothers : ∀ C : OffCorridorComponent P, C ≠ Cstar →
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2)
    (hbase : ∀ r ∈ Finset.range P.length, r ≠ j →
      coverMultiplicity
        (Finset.univ : Finset (OffCorridorComponent P))
        (offCorridorComponentIntervalEdges P) r = 1) :
    Set.InjOn (G.dist w) (offCorridorFinset P : Set V) := by
  classical
  intro x hx y hy hxy
  have hxNot : x ∉ P.support := by
    have hxSupportFinset := (Finset.mem_sdiff.mp hx).2
    simpa [supportFinset] using hxSupportFinset
  have hyNot : y ∉ P.support := by
    have hySupportFinset := (Finset.mem_sdiff.mp hy).2
    simpa [supportFinset] using hySupportFinset
  let Cx := offCorridorComponentOf P x hxNot
  let Cy := offCorridorComponentOf P y hyNot
  have hxC : x ∈ offCorridorComponentFinset Cx :=
    mem_offCorridorComponentOf P hxNot
  have hyC : y ∈ offCorridorComponentFinset Cy :=
    mem_offCorridorComponentOf P hyNot
  by_cases hcomp : Cx = Cy
  · have hyCx : y ∈ offCorridorComponentFinset Cx := by
      simpa [hcomp] using hyC
    by_cases hxStar : Cx = Cstar
    · have hxCases : x = cL ∨ x = cR := by
        simpa [hxStar, hstar] using hxC
      have hyCases : y = cL ∨ y = cR := by
        simpa [hxStar, hstar] using hyCx
      rcases hxCases with rfl | rfl <;>
        rcases hyCases with rfl | rfl
      · rfl
      · rw [hlevelL, hlevelR] at hxy
        omega
      · rw [hlevelR, hlevelL] at hxy
        omega
      · rfl
    · have hcard : (offCorridorComponentFinset Cx).card ≤ 1 := by
        rw [(hothers Cx hxStar).1]
      exact (Finset.card_le_one.mp hcard) x hxC y hyCx
  · have hxCoordinates :=
      IsGeodesic.massOverlap_vertex_adjacent_interval_coordinates
        hconn hP Cstar Cx a hstar hlevelL hlevelR hstarInterval
          hothers hxC
    have hyCoordinates :=
      IsGeodesic.massOverlap_vertex_adjacent_interval_coordinates
        hconn hP Cstar Cy a hstar hlevelL hlevelR hstarInterval
          hothers hyC
    have hyPrev : G.dist w x - 1 ∈
        offCorridorComponentIntervalEdges P Cy := by
      rw [hxy]
      exact hyCoordinates.2.1
    have hyHere : G.dist w x ∈
        offCorridorComponentIntervalEdges P Cy := by
      rw [hxy]
      exact hyCoordinates.2.2
    have htwoLe (r : ℕ)
        (hrx : r ∈ offCorridorComponentIntervalEdges P Cx)
        (hry : r ∈ offCorridorComponentIntervalEdges P Cy) :
        2 ≤ coverMultiplicity
          (Finset.univ : Finset (OffCorridorComponent P))
          (offCorridorComponentIntervalEdges P) r := by
      have hpairSub : ({Cx, Cy} : Finset (OffCorridorComponent P)) ⊆
          (Finset.univ : Finset (OffCorridorComponent P)).filter
            (fun C => r ∈ offCorridorComponentIntervalEdges P C) := by
        intro C hC
        have hcases : C = Cx ∨ C = Cy := by simpa using hC
        rcases hcases with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨by simp, hrx⟩
        · exact Finset.mem_filter.mpr ⟨by simp, hry⟩
      have hpairCard : ({Cx, Cy} :
          Finset (OffCorridorComponent P)).card = 2 := by
        simp [hcomp]
      rw [coverMultiplicity_eq_card_filter]
      rw [← hpairCard]
      exact Finset.card_le_card hpairSub
    have hprevRange : G.dist w x - 1 ∈ Finset.range P.length :=
      offCorridorComponentIntervalEdges_subset_range P Cx
        hxCoordinates.2.1
    have hhereRange : G.dist w x ∈ Finset.range P.length :=
      offCorridorComponentIntervalEdges_subset_range P Cx
        hxCoordinates.2.2
    have hprevTwo := htwoLe (G.dist w x - 1)
      hxCoordinates.2.1 hyPrev
    have hhereTwo := htwoLe (G.dist w x)
      hxCoordinates.2.2 hyHere
    have hprevJ : G.dist w x - 1 = j := by
      by_contra hne
      have hone := hbase (G.dist w x - 1) hprevRange hne
      omega
    have hhereJ : G.dist w x = j := by
      by_contra hne
      have hone := hbase (G.dist w x) hhereRange hne
      omega
    omega

set_option maxHeartbeats 800000
/-- In the mixed mass-overlap shape, the adjacent off-level fibers count
interval multiplicity, except that the middle gap of the saturated
span-three pair sees both of its vertices and therefore contributes one
additional unit. -/
theorem IsGeodesic.coverMultiplicity_add_pairMiddle_eq_adjacent_offLevelFiber_cards
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    [Fintype (OffCorridorComponent P)]
    (hconn : G.Connected) (color : G.Coloring Bool) (hP : IsGeodesic P)
    (Cstar : OffCorridorComponent P) (a r : ℕ)
    (hstarSize : (offCorridorComponentFinset Cstar).card = 2)
    (hstarInterval : offCorridorComponentIntervalEdges P Cstar =
      Finset.Ico a (a + 3))
    (hothers : ∀ C : OffCorridorComponent P, C ≠ Cstar →
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2) :
    coverMultiplicity
        (Finset.univ : Finset (OffCorridorComponent P))
        (offCorridorComponentIntervalEdges P) r +
        (if r = a + 1 then 1 else 0) =
      (offLevelFiber P (G.dist w) r).card +
        (offLevelFiber P (G.dist w) (r + 1)).card := by
  classical
  obtain ⟨cL, cR, hstar, hne, _hadj, _hleft, _hright,
      hlevelL, hlevelR⟩ :=
    IsGeodesic.pair_spanThree_geometry
      hconn color hP Cstar a hstarSize hstarInterval
  have hdelta :
      (if r = a + 1 then 1 else 0) =
        ∑ C : OffCorridorComponent P,
          if C = Cstar ∧ r = a + 1 then 1 else 0 := by
    by_cases hr : r = a + 1 <;> simp [hr]
  calc
    coverMultiplicity
          (Finset.univ : Finset (OffCorridorComponent P))
          (offCorridorComponentIntervalEdges P) r +
          (if r = a + 1 then 1 else 0) =
        (∑ C : OffCorridorComponent P,
          if r ∈ offCorridorComponentIntervalEdges P C then 1 else 0) +
          ∑ C : OffCorridorComponent P,
            if C = Cstar ∧ r = a + 1 then 1 else 0 := by
      rw [hdelta, coverMultiplicity_eq_card_filter]
      simp
    _ = ∑ C : OffCorridorComponent P,
        ((if r ∈ offCorridorComponentIntervalEdges P C then 1 else 0) +
          if C = Cstar ∧ r = a + 1 then 1 else 0) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ C : OffCorridorComponent P,
        (((offCorridorComponentFinset C).filter
          fun v => G.dist w v = r).card +
        ((offCorridorComponentFinset C).filter
          fun v => G.dist w v = r + 1).card) := by
      apply Finset.sum_congr rfl
      intro C _
      by_cases hC : C = Cstar
      · subst C
        simp only [hstarInterval, hstar, hlevelL, hlevelR,
          Finset.mem_Ico, Finset.filter_insert, Finset.filter_singleton]
        split_ifs <;> simp [hne] at * <;> omega
      · obtain ⟨hsize, hspan⟩ := hothers C hC
        obtain ⟨l, hinterval⟩ :=
          offCorridorInterval_eq_Ico_of_card_eq_two P C hspan
        obtain ⟨c, hset, hlevel, _hleft, _hright⟩ :=
          IsGeodesic.singleton_spanTwo_geometry
            hconn hP C l hsize hinterval
        simp only [hC, false_and, if_false, hinterval, hset, hlevel,
          Finset.mem_Ico, Finset.filter_singleton]
        split_ifs <;> simp at * <;> omega
    _ = (offLevelFiber P (G.dist w) r).card +
        (offLevelFiber P (G.dist w) (r + 1)).card := by
      rw [Finset.sum_add_distrib]
      rw [← offLevelFiber_card_eq_sum_componentLevelFiber_card,
        ← offLevelFiber_card_eq_sum_componentLevelFiber_card]

set_option maxHeartbeats 200000
set_option maxRecDepth 1000

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

/-- The exact two-high threshold profile induced by the distinguished
span-three pair and the unique overlap coordinate. -/
theorem IsGeodesic.massOverlap_twoHighCapacityProfile
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    [Fintype (OffCorridorComponent P)]
    (hconn : G.Connected) (color : G.Coloring Bool) (hP : IsGeodesic P)
    (htwo : P.length = 2 * slack P - 2)
    (hs : 5 ≤ slack P)
    (Cstar : OffCorridorComponent P) (a j : ℕ)
    (hstarSize : (offCorridorComponentFinset Cstar).card = 2)
    (hstarInterval : offCorridorComponentIntervalEdges P Cstar =
      Finset.Ico a (a + 3))
    (hothers : ∀ C : OffCorridorComponent P, C ≠ Cstar →
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2)
    (hjRange : j ∈ Finset.range P.length)
    (hjTwo : coverMultiplicity
      (Finset.univ : Finset (OffCorridorComponent P))
      (offCorridorComponentIntervalEdges P) j = 2)
    (hbase : ∀ r ∈ Finset.range P.length, r ≠ j →
      coverMultiplicity
        (Finset.univ : Finset (OffCorridorComponent P))
        (offCorridorComponentIntervalEdges P) r = 1)
    (hjne : j ≠ a + 1)
    (hbinary : ∀ k : ℕ,
      (offLevelFiber P (G.dist w) k).card ≤ 1) :
    let extra : ℕ → ℕ := fun k =>
      (offLevelFiber P (G.dist w) k).card
    let weight : Fin P.length → ℕ := fun r =>
      extra r.1 + extra (r.1 + 1)
    let capacity : Fin P.length → ℕ := fun r =>
      weight r + extra r.1 * extra (r.1 + 1)
    ∃ highFin : Finset (Fin P.length),
      highFin.card = 2 ∧
      (∀ r : Fin P.length,
        r ∈ highFin ↔ r.1 = a + 1 ∨ r.1 = j) ∧
      (∀ r : Fin P.length,
        weight r = if r ∈ highFin then 2 else 1) ∧
      (∑ r : Fin P.length, weight r) = 2 * slack P ∧
      (∑ r : Fin P.length, extra r.1 * extra (r.1 + 1)) ≤ 2 ∧
      (∀ r : Fin P.length, capacity r ≤ (weight r) ^ 2) ∧
      (∀ r : Fin P.length,
        capacity r ≤ if r ∈ highFin then 3 else 1) ∧
      (∑ r : Fin P.length, capacity r) ≤ 2 * slack P + 2 ∧
      (∑ r : Fin P.length, ∑ q : Fin P.length,
        min (capacity r) (capacity q)) ≤ P.length ^ 2 + 8 := by
  classical
  let extra : ℕ → ℕ := fun k =>
    (offLevelFiber P (G.dist w) k).card
  let weight : Fin P.length → ℕ := fun r =>
    extra r.1 + extra (r.1 + 1)
  let capacity : Fin P.length → ℕ := fun r =>
    weight r + extra r.1 * extra (r.1 + 1)
  have haMidMem : a + 1 ∈ offCorridorComponentIntervalEdges P Cstar := by
    rw [hstarInterval]
    simp
  have haMidRange : a + 1 ∈ Finset.range P.length :=
    offCorridorComponentIntervalEdges_subset_range P Cstar haMidMem
  let aMid : Fin P.length := ⟨a + 1, Finset.mem_range.mp haMidRange⟩
  let jFin : Fin P.length := ⟨j, Finset.mem_range.mp hjRange⟩
  let highFin : Finset (Fin P.length) := {aMid, jFin}
  have haMidNeJ : aMid ≠ jFin := by
    intro h
    have hval := congrArg Fin.val h
    exact hjne hval.symm
  have hhighCard : highFin.card = 2 := by
    simp [highFin, haMidNeJ]
  have hhighMem (r : Fin P.length) :
      r ∈ highFin ↔ r.1 = a + 1 ∨ r.1 = j := by
    constructor
    · intro hr
      have hrCases : r = aMid ∨ r = jFin := by
        simpa [highFin] using hr
      rcases hrCases with hra | hrj
      · left
        have := congrArg Fin.val hra
        simpa [aMid] using this
      · right
        have := congrArg Fin.val hrj
        simpa [jFin] using this
    · intro hr
      rcases hr with hra | hrj
      · have hre : r = aMid := by
          apply Fin.ext
          simpa [aMid] using hra
        simp [highFin, hre]
      · have hre : r = jFin := by
          apply Fin.ext
          simpa [jFin] using hrj
        simp [highFin, hre]
  have hweightNat (r : ℕ) (hr : r ∈ Finset.range P.length) :
      extra r + extra (r + 1) =
        if r = a + 1 ∨ r = j then 2 else 1 := by
    have hrel :=
      IsGeodesic.coverMultiplicity_add_pairMiddle_eq_adjacent_offLevelFiber_cards
        hconn color hP Cstar a r hstarSize hstarInterval hothers
    change coverMultiplicity
          (Finset.univ : Finset (OffCorridorComponent P))
          (offCorridorComponentIntervalEdges P) r +
          (if r = a + 1 then 1 else 0) =
        extra r + extra (r + 1) at hrel
    by_cases hra : r = a + 1
    · have hrj : r ≠ j := by
        intro hrj
        exact hjne (hrj.symm.trans hra)
      have hone := hbase r hr hrj
      rw [if_pos (Or.inl hra)]
      rw [if_pos hra, hone] at hrel
      omega
    · by_cases hrj : r = j
      · subst r
        rw [if_pos (Or.inr rfl)]
        rw [if_neg (by exact hjne), hjTwo] at hrel
        omega
      · have hone := hbase r hr hrj
        rw [if_neg (by tauto)]
        rw [if_neg hra, hone] at hrel
        omega
  have hweightProfile (r : Fin P.length) :
      weight r = if r ∈ highFin then 2 else 1 := by
    have h := hweightNat r.1 (Finset.mem_range.mpr r.2)
    by_cases hr : r ∈ highFin
    · have hor := (hhighMem r).1 hr
      rw [if_pos hr]
      simpa [weight, hor] using h
    · have hn : ¬(r.1 = a + 1 ∨ r.1 = j) := by
        exact fun hor => hr ((hhighMem r).2 hor)
      rw [if_neg hr]
      simpa [weight, hn] using h
  have hweightSum : (∑ r : Fin P.length, weight r) =
      2 * slack P := by
    calc
      (∑ r : Fin P.length, weight r) =
          ∑ r : Fin P.length,
            (1 + if r ∈ highFin then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [hweightProfile]
        by_cases hr : r ∈ highFin <;> simp [hr]
      _ = P.length + highFin.card := by
        rw [Finset.sum_add_distrib]
        simp
      _ = P.length + 2 := by rw [hhighCard]
      _ = 2 * slack P := by omega
  have hproductPoint (r : Fin P.length) :
      extra r.1 * extra (r.1 + 1) ≤
        if r ∈ highFin then 1 else 0 := by
    have hw := hweightProfile r
    have hx : extra r.1 ≤ 1 := by simpa [extra] using hbinary r.1
    have hy : extra (r.1 + 1) ≤ 1 := by
      simpa [extra] using hbinary (r.1 + 1)
    by_cases hr : r ∈ highFin
    · rw [if_pos hr] at hw ⊢
      interval_cases extra r.1 <;>
        interval_cases extra (r.1 + 1) <;> omega
    · rw [if_neg hr] at hw ⊢
      have hsum : extra r.1 + extra (r.1 + 1) = 1 := by
        simpa [weight] using hw
      interval_cases extra r.1 <;>
        interval_cases extra (r.1 + 1) <;> omega
  have hproductSum :
      (∑ r : Fin P.length, extra r.1 * extra (r.1 + 1)) ≤ 2 := by
    calc
      (∑ r : Fin P.length, extra r.1 * extra (r.1 + 1)) ≤
          ∑ r : Fin P.length, if r ∈ highFin then 1 else 0 :=
        Finset.sum_le_sum fun r _ => hproductPoint r
      _ = highFin.card := by simp
      _ ≤ 2 := by rw [hhighCard]
  have hcapacitySq (r : Fin P.length) :
      capacity r ≤ (weight r) ^ 2 := by
    exact adjacentExtraCapacity_le_sum_sq
      (extra r.1) (extra (r.1 + 1))
  have hcapacityProfile (r : Fin P.length) :
      capacity r ≤ if r ∈ highFin then 3 else 1 := by
    have hw := hweightProfile r
    have hp := hproductPoint r
    change weight r + extra r.1 * extra (r.1 + 1) ≤
      if r ∈ highFin then 3 else 1
    by_cases hr : r ∈ highFin
    · have hw' : weight r = 2 := by simpa [hr] using hw
      have hp' : extra r.1 * extra (r.1 + 1) ≤ 1 := by
        simpa [hr] using hp
      rw [if_pos hr]
      omega
    · have hw' : weight r = 1 := by simpa [hr] using hw
      have hp' : extra r.1 * extra (r.1 + 1) ≤ 0 := by
        simpa [hr] using hp
      rw [if_neg hr]
      omega
  have haggregate := twoHighColumns_fin_profile_bounds
    P.length capacity highFin hhighCard.le hcapacityProfile
  refine ⟨highFin, hhighCard, hhighMem, hweightProfile, hweightSum,
    hproductSum, hcapacitySq, hcapacityProfile, ?_, haggregate.2⟩
  calc
    (∑ r : Fin P.length, capacity r) ≤ P.length + 4 := haggregate.1
    _ = 2 * slack P + 2 := by omega

set_option maxHeartbeats 200000
set_option maxRecDepth 1000

/-- Outside the saturated span-three pair in the mixed mass-overlap shape,
every vertex has the two ordinary corridor anchors dictated by its rooted
level. -/
theorem IsGeodesic.massOverlap_regular_twoSidedAnchors
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ v cL cR : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P)
    (Cstar : OffCorridorComponent P)
    (hstar : offCorridorComponentFinset Cstar = {cL, cR})
    (hothers : ∀ C : OffCorridorComponent P, C ≠ Cstar →
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2)
    (hvL : v ≠ cL) (hvR : v ≠ cR) :
    (G.dist w v < P.length →
      G.Adj v (P.getVert (G.dist w v + 1))) ∧
    (0 < G.dist w v →
      G.Adj (P.getVert (G.dist w v - 1)) v) := by
  exact IsGeodesic.q2q2PureMass_regular_twoSidedAnchors
    (v := v) hconn hP Cstar Cstar hstar hstar
    (fun C hC _ ↦ hothers C hC) hvL hvR hvL hvR

/-- A pair from the right vertex of the span-three block to a regular
vertex is aligned, except possibly at the left contact level. -/
theorem IsGeodesic.massOverlap_cR_regular_levelAligned_or_leftContact
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ y cL cR : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P)
    (Cstar : OffCorridorComponent P) (a : ℕ)
    (hstar : offCorridorComponentFinset Cstar = {cL, cR})
    (hothers : ∀ C : OffCorridorComponent P, C ≠ Cstar →
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2)
    (hLR : G.Adj cL cR)
    (hleft : G.Adj cL (P.getVert a))
    (hright : G.Adj cR (P.getVert (a + 3)))
    (hlevelR : G.dist w cR = a + 2)
    (hlength : a + 3 ≤ P.length)
    (hyL : y ≠ cL) (hyR : y ≠ cR)
    (hyBound : G.dist w y ≤ P.length)
    (hlevelEven : Even (Nat.dist (G.dist w cR) (G.dist w y)))
    (hlegal : 4 ≤ G.dist cR y) :
    G.dist cR y = Nat.dist (G.dist w cR) (G.dist w y) ∨
      (G.dist w y = a ∧ y ∈ offCorridorFinset P) := by
  have hyAnchors := IsGeodesic.massOverlap_regular_twoSidedAnchors
    (v := y) hconn hP Cstar hstar hothers hyL hyR
  have hlower := bfsLevel_natDist_le hconn w cR y
  rcases lt_trichotomy (G.dist w y) (a + 2) with hlt | heq | hgt
  · have heven : Even ((a + 2) - G.dist w y) := by
      simpa [hlevelR, Nat.dist_eq_sub_of_le_right hlt.le] using hlevelEven
    obtain ⟨q, hq⟩ := heven
    by_cases hcontact : G.dist w y = a
    · right
      refine ⟨hcontact, ?_⟩
      by_contra hyOff
      have hySupport : y ∈ P.support := by
        by_contra hyNot
        have : y ∈ offCorridorFinset P := by
          exact Finset.mem_sdiff.mpr
            ⟨Finset.mem_univ y, by simpa [supportFinset] using hyNot⟩
        exact hyOff this
      have hyEq := IsGeodesic.eq_getVert_of_mem_support_rootDist_eq
        hP hySupport hcontact
      have hCRCL : G.dist cR cL = 1 :=
        dist_eq_one_iff_adj.mpr hLR.symm
      have hCLP : G.dist cL (P.getVert a) = 1 :=
        dist_eq_one_iff_adj.mpr hleft
      have htri := hconn.dist_triangle
        (u := cR) (v := cL) (w := P.getVert a)
      rw [hCRCL, hCLP] at htri
      rw [hyEq] at hlegal
      omega
    · left
      have hyNext := hyAnchors.1 (by omega)
      have hgap : G.dist w y + 1 ≤ a := by omega
      have hcorr := hP.dist_getVert_eq_sub
        (i := G.dist w y + 1) (j := a) hgap (by omega)
      rw [SimpleGraph.dist_comm] at hcorr
      have hCRCL : G.dist cR cL = 1 :=
        dist_eq_one_iff_adj.mpr hLR.symm
      have hCLP : G.dist cL (P.getVert a) = 1 :=
        dist_eq_one_iff_adj.mpr hleft
      have hPY : G.dist (P.getVert (G.dist w y + 1)) y = 1 :=
        dist_eq_one_iff_adj.mpr hyNext.symm
      have htri₁ := hconn.dist_triangle (u := cR) (v := cL) (w := y)
      have htri₂ := hconn.dist_triangle
        (u := cL) (v := P.getVert a) (w := y)
      have htri₃ := hconn.dist_triangle
        (u := P.getVert a)
        (v := P.getVert (G.dist w y + 1)) (w := y)
      rw [hCRCL] at htri₁
      rw [hCLP] at htri₂
      rw [hcorr, hPY] at htri₃
      rw [hlevelR, Nat.dist_eq_sub_of_le_right hlt.le] at hlower ⊢
      omega
  · have hyNext := hyAnchors.1 (by omega)
    have hyNext' : G.Adj y (P.getVert (a + 3)) := by
      simpa [heq] using hyNext
    have hCRP : G.dist cR (P.getVert (a + 3)) = 1 :=
      dist_eq_one_iff_adj.mpr hright
    have hPY : G.dist (P.getVert (a + 3)) y = 1 :=
      dist_eq_one_iff_adj.mpr hyNext'.symm
    have htri := hconn.dist_triangle
      (u := cR) (v := P.getVert (a + 3)) (w := y)
    rw [hCRP, hPY] at htri
    omega
  · left
    have heven : Even (G.dist w y - (a + 2)) := by
      simpa [hlevelR, Nat.dist_eq_sub_of_le hgt.le] using hlevelEven
    obtain ⟨q, hq⟩ := heven
    have hgap : a + 2 + 2 ≤ G.dist w y := by omega
    have hyPrev := hyAnchors.2 (by omega)
    have hupper := IsGeodesic.dist_le_levelSub_of_adjacent_corridorAnchors
      hconn hP hgap hyBound (by simpa using hright) hyPrev
    rw [hlevelR, Nat.dist_eq_sub_of_le hgt.le] at hlower ⊢
    omega

/-- A pair from the left vertex of the span-three block to a regular
vertex is aligned, except possibly at the right contact level. -/
theorem IsGeodesic.massOverlap_cL_regular_levelAligned_or_rightContact
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ y cL cR : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P)
    (Cstar : OffCorridorComponent P) (a : ℕ)
    (hstar : offCorridorComponentFinset Cstar = {cL, cR})
    (hothers : ∀ C : OffCorridorComponent P, C ≠ Cstar →
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2)
    (hLR : G.Adj cL cR)
    (hleft : G.Adj cL (P.getVert a))
    (hright : G.Adj cR (P.getVert (a + 3)))
    (hlevelL : G.dist w cL = a + 1)
    (hlength : a + 3 ≤ P.length)
    (hyL : y ≠ cL) (hyR : y ≠ cR)
    (hyBound : G.dist w y ≤ P.length)
    (hlevelEven : Even (Nat.dist (G.dist w cL) (G.dist w y)))
    (hlegal : 4 ≤ G.dist cL y) :
    G.dist cL y = Nat.dist (G.dist w cL) (G.dist w y) ∨
      (G.dist w y = a + 3 ∧ y ∈ offCorridorFinset P) := by
  have hyAnchors := IsGeodesic.massOverlap_regular_twoSidedAnchors
    (v := y) hconn hP Cstar hstar hothers hyL hyR
  have hlower := bfsLevel_natDist_le hconn w cL y
  rcases lt_trichotomy (G.dist w y) (a + 1) with hlt | heq | hgt
  · left
    have heven : Even ((a + 1) - G.dist w y) := by
      simpa [hlevelL, Nat.dist_eq_sub_of_le_right hlt.le] using hlevelEven
    obtain ⟨q, hq⟩ := heven
    have hgap : G.dist w y + 2 ≤ a + 1 := by omega
    have hyNext := hyAnchors.1 (by omega)
    have hupperRaw :=
      IsGeodesic.dist_le_levelSub_of_adjacent_corridorAnchors
        hconn hP hgap (by omega : a + 1 ≤ P.length) hyNext
        (by simpa using hleft.symm)
    rw [SimpleGraph.dist_comm] at hupperRaw
    rw [hlevelL, Nat.dist_eq_sub_of_le_right hlt.le] at hlower ⊢
    omega
  · have hyPrev := hyAnchors.2 (by omega)
    have hyPrev' : G.Adj (P.getVert a) y := by
      simpa [heq] using hyPrev
    have hCLP : G.dist cL (P.getVert a) = 1 :=
      dist_eq_one_iff_adj.mpr hleft
    have hPY : G.dist (P.getVert a) y = 1 :=
      dist_eq_one_iff_adj.mpr hyPrev'
    have htri := hconn.dist_triangle
      (u := cL) (v := P.getVert a) (w := y)
    rw [hCLP, hPY] at htri
    omega
  · have heven : Even (G.dist w y - (a + 1)) := by
      simpa [hlevelL, Nat.dist_eq_sub_of_le hgt.le] using hlevelEven
    obtain ⟨q, hq⟩ := heven
    by_cases hcontact : G.dist w y = a + 3
    · right
      refine ⟨hcontact, ?_⟩
      by_contra hyOff
      have hySupport : y ∈ P.support := by
        by_contra hyNot
        have : y ∈ offCorridorFinset P := by
          exact Finset.mem_sdiff.mpr
            ⟨Finset.mem_univ y, by simpa [supportFinset] using hyNot⟩
        exact hyOff this
      have hyEq := IsGeodesic.eq_getVert_of_mem_support_rootDist_eq
        hP hySupport hcontact
      have hCLCR : G.dist cL cR = 1 :=
        dist_eq_one_iff_adj.mpr hLR
      have hCRP : G.dist cR (P.getVert (a + 3)) = 1 :=
        dist_eq_one_iff_adj.mpr hright
      have htri := hconn.dist_triangle
        (u := cL) (v := cR) (w := P.getVert (a + 3))
      rw [hCLCR, hCRP] at htri
      rw [hyEq] at hlegal
      omega
    · left
      have hyPrev := hyAnchors.2 (by omega)
      have hgap : a + 3 ≤ G.dist w y - 1 := by omega
      have hcorr := hP.dist_getVert_eq_sub
        (i := a + 3) (j := G.dist w y - 1) hgap (by omega)
      have hCLCR : G.dist cL cR = 1 :=
        dist_eq_one_iff_adj.mpr hLR
      have hCRP : G.dist cR (P.getVert (a + 3)) = 1 :=
        dist_eq_one_iff_adj.mpr hright
      have hPY : G.dist (P.getVert (G.dist w y - 1)) y = 1 :=
        dist_eq_one_iff_adj.mpr hyPrev
      have htri₁ := hconn.dist_triangle (u := cL) (v := cR) (w := y)
      have htri₂ := hconn.dist_triangle
        (u := cR) (v := P.getVert (a + 3)) (w := y)
      have htri₃ := hconn.dist_triangle
        (u := P.getVert (a + 3))
        (v := P.getVert (G.dist w y - 1)) (w := y)
      rw [hCLCR] at htri₁
      rw [hCRP] at htri₂
      rw [hcorr, hPY] at htri₃
      rw [hlevelL, Nat.dist_eq_sub_of_le hgt.le] at hlower ⊢
      omega

/-- Every legal same-side pair in the mixed mass-overlap geometry is level
aligned except for one of the two literal contact positions. -/
theorem IsGeodesic.massOverlap_levelAligned_or_contact
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ x y cL cR : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P)
    (Cstar : OffCorridorComponent P) (a : ℕ)
    (hstar : offCorridorComponentFinset Cstar = {cL, cR})
    (hothers : ∀ C : OffCorridorComponent P, C ≠ Cstar →
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2)
    (hLR : G.Adj cL cR)
    (hleft : G.Adj cL (P.getVert a))
    (hright : G.Adj cR (P.getVert (a + 3)))
    (hlevelL : G.dist w cL = a + 1)
    (hlevelR : G.dist w cR = a + 2)
    (hlength : a + 3 ≤ P.length)
    (hxBound : G.dist w x ≤ P.length)
    (hyBound : G.dist w y ≤ P.length)
    (hlevelEven : Even (Nat.dist (G.dist w x) (G.dist w y)))
    (hlegal : 4 ≤ G.dist x y) :
    G.dist x y = Nat.dist (G.dist w x) (G.dist w y) ∨
      (∃ z ∈ offCorridorFinset P,
        G.dist w z = a ∧ PairMatches x y z cR) ∨
      (∃ z ∈ offCorridorFinset P,
        G.dist w z = a + 3 ∧ PairMatches x y cL z) := by
  by_cases hxL : x = cL
  · subst x
    by_cases hyL : y = cL
    · subst y
      simp at hlegal
    · by_cases hyR : y = cR
      · subst y
        have hdist : G.dist cL cR = 1 := dist_eq_one_iff_adj.mpr hLR
        omega
      · have h := IsGeodesic.massOverlap_cL_regular_levelAligned_or_rightContact
          hconn hP Cstar a hstar hothers hLR hleft hright hlevelL hlength
          hyL hyR hyBound hlevelEven hlegal
        rcases h with haligned | ⟨hylevel, hyOff⟩
        · exact Or.inl haligned
        · right; right
          exact ⟨y, hyOff, hylevel, by simp [PairMatches]⟩
  · by_cases hxR : x = cR
    · subst x
      by_cases hyL : y = cL
      · subst y
        have hdist : G.dist cR cL = 1 := dist_eq_one_iff_adj.mpr hLR.symm
        omega
      · by_cases hyR : y = cR
        · subst y
          simp at hlegal
        · have h := IsGeodesic.massOverlap_cR_regular_levelAligned_or_leftContact
            hconn hP Cstar a hstar hothers hLR hleft hright hlevelR hlength
            hyL hyR hyBound hlevelEven hlegal
          rcases h with haligned | ⟨hylevel, hyOff⟩
          · exact Or.inl haligned
          · right; left
            exact ⟨y, hyOff, hylevel, by simp [PairMatches]⟩
    · by_cases hyL : y = cL
      · subst y
        have h := IsGeodesic.massOverlap_cL_regular_levelAligned_or_rightContact
          hconn hP Cstar a hstar hothers hLR hleft hright hlevelL hlength
          hxL hxR hxBound
          (by simpa [Nat.dist_comm] using hlevelEven)
          (by simpa [SimpleGraph.dist_comm] using hlegal)
        rcases h with haligned | ⟨hxlevel, hxOff⟩
        · left
          simpa [SimpleGraph.dist_comm, Nat.dist_comm] using haligned
        · right; right
          exact ⟨x, hxOff, hxlevel, by simp [PairMatches]⟩
      · by_cases hyR : y = cR
        · subst y
          have h := IsGeodesic.massOverlap_cR_regular_levelAligned_or_leftContact
            hconn hP Cstar a hstar hothers hLR hleft hright hlevelR hlength
            hxL hxR hxBound
            (by simpa [Nat.dist_comm] using hlevelEven)
            (by simpa [SimpleGraph.dist_comm] using hlegal)
          rcases h with haligned | ⟨hxlevel, hxOff⟩
          · left
            simpa [SimpleGraph.dist_comm, Nat.dist_comm] using haligned
          · right; left
            exact ⟨x, hxOff, hxlevel, by simp [PairMatches]⟩
        · left
          have hxAnchors :=
            IsGeodesic.massOverlap_regular_twoSidedAnchors
              (v := x) hconn hP Cstar hstar hothers hxL hxR
          have hyAnchors :=
            IsGeodesic.massOverlap_regular_twoSidedAnchors
              (v := y) hconn hP Cstar hstar hothers hyL hyR
          exact IsGeodesic.levelAligned_of_twoSidedAnchors
            hconn hP hxAnchors.1 hxAnchors.2 hyAnchors.1 hyAnchors.2
            hxBound hyBound hlevelEven hlegal

/-- A geodesic BFS layer is the corridor vertex at that coordinate together
with the off-corridor fiber on the same rooted level. -/
theorem IsGeodesic.levelLayer_eq_insert_getVert_offLevelFiber
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ : V} {P : G.Walk w x₀}
    (hP : IsGeodesic P) {k : ℕ} (hk : k ≤ P.length) :
    levelLayer (G.dist w) k =
      insert (P.getVert k) (offLevelFiber P (G.dist w) k) := by
  classical
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
      exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_filter.mpr ⟨hvOff, hvLevel⟩))
  · intro hv
    rcases Finset.mem_insert.mp hv with hvPath | hvOff
    · subst v
      have hlevel : G.dist w (P.getVert k) = k := by
        simpa using hP.dist_getVert_eq_sub (i := 0) (j := k)
          (by omega) hk
      simpa using hlevel
    · have hvData := Finset.mem_filter.mp hvOff
      simpa [levelLayer, hvData.2]

/-- A cut whose oriented crossing-edge classifier has at most two outputs
has capacity at most two. -/
theorem cutSize_le_two_of_two_crossing_pairs
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (T : Finset V) (x₁ y₁ x₂ y₂ : V)
    (hclass : ∀ x ∈ T, ∀ y ∉ T, G.Adj x y →
      (x = x₁ ∧ y = y₁) ∨ (x = x₂ ∧ y = y₂)) :
    cutSize G T ≤ 2 := by
  classical
  let crossingPairs := T.sigma fun x => G.neighborFinset x \ T
  let allowed : Finset (Sigma fun _ : V => V) :=
    {⟨x₁, y₁⟩, ⟨x₂, y₂⟩}
  have hsubset : crossingPairs ⊆ allowed := by
    intro e he
    obtain ⟨x, y⟩ := e
    have heData : x ∈ T ∧ y ∈ G.neighborFinset x \ T := by
      simpa [crossingPairs] using he
    have hyData : G.Adj x y ∧ y ∉ T := by
      simpa using heData.2
    rcases hclass x heData.1 y hyData.2 hyData.1 with h₁ | h₂
    · simp [allowed, h₁.1, h₁.2]
    · simp [allowed, h₂.1, h₂.2]
  calc
    cutSize G T = crossingPairs.card := by
      simp [cutSize, crossingPairs, Finset.card_sigma]
    _ ≤ allowed.card := Finset.card_le_card hsubset
    _ ≤ 2 := Finset.card_le_two

/-- At a left-contact mass-overlap block, inserting its right pair vertex
into the upper level cut leaves only the internal pair edge and one corridor
edge crossing. -/
theorem cutSize_insert_rightVertex_levelUpperCut_le_two
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (level : V → ℕ) (a : ℕ) (p₂ p₃ R L : V)
    (hstep : ∀ {u v : V}, G.Adj u v →
      Nat.dist (level u) (level v) = 1)
    (hlevelR : level R = a + 2)
    (hlevelL : level L = a + 1)
    (hfiber₂ : levelLayer level (a + 2) = {p₂, R})
    (hfiber₃ : levelLayer level (a + 3) = {p₃})
    (hneighborsR : ∀ y : V, G.Adj R y → y = L ∨ y = p₃) :
    cutSize G (insert R (levelUpperCut level (a + 2))) ≤ 2 := by
  classical
  let U := levelUpperCut level (a + 2)
  let T := insert R U
  have hclass : ∀ x ∈ T, ∀ y ∉ T, G.Adj x y →
      (x = R ∧ y = L) ∨ (x = p₃ ∧ y = p₂) := by
    intro x hx y hy hxy
    by_cases hxR : x = R
    · subst x
      rcases hneighborsR y hxy with hyL | hyp₃
      · exact Or.inl ⟨rfl, hyL⟩
      · subst y
        have hp₃Layer : p₃ ∈ levelLayer level (a + 3) := by
          rw [hfiber₃]
          simp
        have hp₃Level : level p₃ = a + 3 := by simpa using hp₃Layer
        have hp₃U : p₃ ∈ U := by
          simp [U, hp₃Level]
        exact (hy (by simp [T, hp₃U])).elim
    · have hxU : x ∈ U := by
        have := Finset.mem_insert.mp hx
        exact this.resolve_left hxR
      have hyU : y ∉ U := by
        intro hyU
        exact hy (Finset.mem_insert_of_mem hyU)
      have hxHigh : a + 2 < level x := by simpa [U] using hxU
      have hyLow : level y ≤ a + 2 := by simpa [U] using hyU
      have hdist := hstep hxy
      rw [Nat.dist_eq_sub_of_le_right (by omega : level y ≤ level x)] at hdist
      have hxLevel : level x = a + 3 := by omega
      have hyLevel : level y = a + 2 := by omega
      have hxLayer : x ∈ levelLayer level (a + 3) := by simpa using hxLevel
      have hyLayer : y ∈ levelLayer level (a + 2) := by simpa using hyLevel
      rw [hfiber₃] at hxLayer
      rw [hfiber₂] at hyLayer
      have hxp₃ : x = p₃ := by simpa using hxLayer
      have hyCases : y = p₂ ∨ y = R := by simpa using hyLayer
      rcases hyCases with hyp₂ | hyR
      · exact Or.inr ⟨hxp₃, hyp₂⟩
      · subst y
        exact (hy (by simp [T])).elim
  simpa [T, U] using
    cutSize_le_two_of_two_crossing_pairs T R L p₃ p₂ hclass

/-- At a right-contact mass-overlap block, inserting the contacting
singleton into the upper level cut leaves its left attachment and one
corridor edge as the only crossings. -/
theorem cutSize_insert_singleton_levelUpperCut_le_two
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (level : V → ℕ) (a : ℕ) (p₂ p₃ p₄ Z : V)
    (hstep : ∀ {u v : V}, G.Adj u v →
      Nat.dist (level u) (level v) = 1)
    (hlevelZ : level Z = a + 3)
    (hlevelp₂ : level p₂ = a + 2)
    (hfiber₃ : levelLayer level (a + 3) = {p₃, Z})
    (hfiber₄ : levelLayer level (a + 4) = {p₄})
    (hneighborsZ : ∀ y : V, G.Adj Z y → y = p₂ ∨ y = p₄) :
    cutSize G (insert Z (levelUpperCut level (a + 3))) ≤ 2 := by
  classical
  let U := levelUpperCut level (a + 3)
  let T := insert Z U
  have hclass : ∀ x ∈ T, ∀ y ∉ T, G.Adj x y →
      (x = Z ∧ y = p₂) ∨ (x = p₄ ∧ y = p₃) := by
    intro x hx y hy hxy
    by_cases hxZ : x = Z
    · subst x
      rcases hneighborsZ y hxy with hyp₂ | hyp₄
      · exact Or.inl ⟨rfl, hyp₂⟩
      · subst y
        have hp₄Layer : p₄ ∈ levelLayer level (a + 4) := by
          rw [hfiber₄]
          simp
        have hp₄Level : level p₄ = a + 4 := by simpa using hp₄Layer
        have hp₄U : p₄ ∈ U := by simp [U, hp₄Level]
        exact (hy (by simp [T, hp₄U])).elim
    · have hxU : x ∈ U := by
        have := Finset.mem_insert.mp hx
        exact this.resolve_left hxZ
      have hyU : y ∉ U := by
        intro hyU
        exact hy (Finset.mem_insert_of_mem hyU)
      have hxHigh : a + 3 < level x := by simpa [U] using hxU
      have hyLow : level y ≤ a + 3 := by simpa [U] using hyU
      have hdist := hstep hxy
      rw [Nat.dist_eq_sub_of_le_right (by omega : level y ≤ level x)] at hdist
      have hxLevel : level x = a + 4 := by omega
      have hyLevel : level y = a + 3 := by omega
      have hxLayer : x ∈ levelLayer level (a + 4) := by simpa using hxLevel
      have hyLayer : y ∈ levelLayer level (a + 3) := by simpa using hyLevel
      rw [hfiber₄] at hxLayer
      rw [hfiber₃] at hyLayer
      have hxp₄ : x = p₄ := by simpa using hxLayer
      have hyCases : y = p₃ ∨ y = Z := by simpa using hyLayer
      rcases hyCases with hyp₃ | hyZ
      · exact Or.inr ⟨hxp₄, hyp₃⟩
      · subst y
        exact (hy (by simp [T])).elim
  simpa [T, U] using
    cutSize_le_two_of_two_crossing_pairs T Z p₂ p₄ p₃ hclass

/-- If an ordinary off-corridor vertex occupies either endpoint level of a
gap covered by the distinguished span-three pair, then that gap is the
unique double-covered coordinate. -/
theorem IsGeodesic.massOverlap_doubleCoordinate_eq_of_contactLevel
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ cL cR z : V} {P : G.Walk w x₀}
    [Fintype (OffCorridorComponent P)]
    (hconn : G.Connected) (hP : IsGeodesic P)
    (Cstar : OffCorridorComponent P) (a j r : ℕ)
    (hstar : offCorridorComponentFinset Cstar = {cL, cR})
    (hstarInterval : offCorridorComponentIntervalEdges P Cstar =
      Finset.Ico a (a + 3))
    (hothers : ∀ C : OffCorridorComponent P, C ≠ Cstar →
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2)
    (hbase : ∀ k ∈ Finset.range P.length, k ≠ j →
      coverMultiplicity
        (Finset.univ : Finset (OffCorridorComponent P))
        (offCorridorComponentIntervalEdges P) k = 1)
    (hrRange : r ∈ Finset.range P.length)
    (hrStar : r ∈ offCorridorComponentIntervalEdges P Cstar)
    (hzoff : z ∈ offCorridorFinset P)
    (hzL : z ≠ cL) (hzR : z ≠ cR)
    (hzLevel : G.dist w z = r ∨ G.dist w z = r + 1) :
    j = r := by
  classical
  have hzNot : z ∉ P.support := by
    have := (Finset.mem_sdiff.mp hzoff).2
    simpa [supportFinset] using this
  let C := offCorridorComponentOf P z hzNot
  have hzC : z ∈ offCorridorComponentFinset C :=
    mem_offCorridorComponentOf P hzNot
  have hCne : C ≠ Cstar := by
    intro hEq
    have hzStar : z ∈ offCorridorComponentFinset Cstar := by
      simpa [hEq] using hzC
    have hzCases : z = cL ∨ z = cR := by simpa [hstar] using hzStar
    exact hzCases.elim hzL hzR
  obtain ⟨hsize, hspan⟩ := hothers C hCne
  obtain ⟨l, hinterval⟩ :=
    offCorridorInterval_eq_Ico_of_card_eq_two P C hspan
  obtain ⟨c, hset, hlevel, _hleft, _hright⟩ :=
    IsGeodesic.singleton_spanTwo_geometry
      hconn hP C l hsize hinterval
  have hzc : z = c := by simpa [hset] using hzC
  have hzLevel' : G.dist w z = l + 1 := by simpa [hzc] using hlevel
  have hrC : r ∈ offCorridorComponentIntervalEdges P C := by
    rw [hinterval]
    rcases hzLevel with hz | hz <;> rw [hz] at hzLevel' <;>
      exact Finset.mem_Ico.mpr (by omega)
  have hpairSub : ({Cstar, C} : Finset (OffCorridorComponent P)) ⊆
      (Finset.univ : Finset (OffCorridorComponent P)).filter
        (fun D => r ∈ offCorridorComponentIntervalEdges P D) := by
    intro D hD
    have hcases : D = Cstar ∨ D = C := by simpa using hD
    rcases hcases with rfl | rfl
    · simp [hrStar]
    · simp [hrC]
  have hpairCard : ({Cstar, C} : Finset (OffCorridorComponent P)).card = 2 := by
    simp [hCne.symm]
  have htwoLe : 2 ≤ coverMultiplicity
      (Finset.univ : Finset (OffCorridorComponent P))
      (offCorridorComponentIntervalEdges P) r := by
    rw [coverMultiplicity_eq_card_filter]
    rw [← hpairCard]
    exact Finset.card_le_card hpairSub
  by_contra hjr
  have hone := hbase r hrRange (Ne.symm hjr)
  omega

/-- For saturated singleton span-two components, covering a corridor gap is
equivalent to the component vertex lying in one of its two endpoint BFS
levels.  Thus interval multiplicity is the sum of the adjacent off-level
fiber cardinalities, including when two components have the same midpoint. -/
theorem IsGeodesic.coverMultiplicity_eq_adjacent_offLevelFiber_cards
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    [Fintype (OffCorridorComponent P)]
    (hconn : G.Connected) (hP : IsGeodesic P)
    (hshape : ∀ C : OffCorridorComponent P,
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2)
    (r : ℕ) :
    coverMultiplicity
        (Finset.univ : Finset (OffCorridorComponent P))
        (offCorridorComponentIntervalEdges P) r =
      (offLevelFiber P (G.dist w) r).card +
        (offLevelFiber P (G.dist w) (r + 1)).card := by
  classical
  calc
    coverMultiplicity
          (Finset.univ : Finset (OffCorridorComponent P))
          (offCorridorComponentIntervalEdges P) r =
        ∑ C : OffCorridorComponent P,
          if r ∈ offCorridorComponentIntervalEdges P C then 1 else 0 := by
      rw [coverMultiplicity_eq_card_filter]
      simp
    _ = ∑ C : OffCorridorComponent P,
        (((offCorridorComponentFinset C).filter
          fun v => G.dist w v = r).card +
        ((offCorridorComponentFinset C).filter
          fun v => G.dist w v = r + 1).card) := by
      apply Finset.sum_congr rfl
      intro C _
      obtain ⟨hsize, hspan⟩ := hshape C
      obtain ⟨l, hinterval⟩ :=
        offCorridorInterval_eq_Ico_of_card_eq_two P C hspan
      obtain ⟨c, hset, hlevel, _hleft, _hright⟩ :=
        IsGeodesic.singleton_spanTwo_geometry
          hconn hP C l hsize hinterval
      simp only [hset, hinterval, hlevel, Finset.mem_Ico,
        Finset.filter_singleton]
      split_ifs <;> simp_all <;> omega
    _ = (offLevelFiber P (G.dist w) r).card +
        (offLevelFiber P (G.dist w) (r + 1)).card := by
      rw [Finset.sum_add_distrib]
      rw [← offLevelFiber_card_eq_sum_componentLevelFiber_card,
        ← offLevelFiber_card_eq_sum_componentLevelFiber_card]

/-- The pure-overlap two-defect shape has an aligned rooted-level demand
matrix.  Its literal threshold columns have total adjacent extra weight
`2s` and adjacent-extra product at most two, even when two singleton
components share one interval. -/
theorem totalCost_le_rlBudget_of_pureOverlap_allNonbridge_sameSide
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    [Fintype (OffCorridorComponent P)]
    (m₁ m₂ : I → V)
    (hconn : G.Connected)
    (color : G.Coloring Bool)
    (hP : IsGeodesic P)
    (htwo : P.length = 2 * slack P - 2)
    (hnonbridge : ∀ i < P.length,
      ¬G.IsBridge s(P.getVert i, P.getVert (i + 1)))
    (hpure :
      let components :=
        (Finset.univ : Finset (OffCorridorComponent P))
      let size : OffCorridorComponent P → ℕ := fun C =>
        (offCorridorComponentFinset C).card
      let span : OffCorridorComponent P → ℕ := fun C =>
        (offCorridorComponentIntervalEdges P C).card
      let unionCard :=
        (components.biUnion
          (offCorridorComponentIntervalEdges P)).card
      PureOverlapShape components size span (slack P) unionCard)
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
  change PureOverlapShape components size span (slack P) unionCard at hpure
  have hshape : ∀ C : OffCorridorComponent P,
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2 := by
    intro C
    have h := hpure.2.2.2 C (by simp [components])
    simpa [size, span, interval] using h
  have hunion : components.biUnion interval = Finset.range P.length := by
    have hraw :=
      IsGeodesic.biUnion_offCorridorIntervals_eq_range hP hnonbridge
    convert hraw using 1
    apply Finset.Subset.antisymm
    · intro r hr
      obtain ⟨C, _hC, hrC⟩ := Finset.mem_biUnion.mp hr
      exact Finset.mem_biUnion.mpr ⟨C, by simp, hrC⟩
    · intro r hr
      obtain ⟨C, _hC, hrC⟩ := Finset.mem_biUnion.mp hr
      exact Finset.mem_biUnion.mpr
        ⟨C, by simp [components], by simpa [interval] using hrC⟩
  have hunionCard : unionCard = P.length := by
    dsimp [unionCard]
    rw [hunion]
    simp
  have hpureLength : PureOverlapShape components
      (fun C => (offCorridorComponentFinset C).card)
      (fun C => (offCorridorComponentIntervalEdges P C).card)
      (slack P) P.length := by
    rw [← hunionCard]
    simpa [size, span, interval] using hpure
  have hcomponentShape : ∀ C : OffCorridorComponent P,
      hasOneDefectShape P C := by
    intro C
    left
    obtain ⟨l, hinterval⟩ :=
      offCorridorInterval_eq_Ico_of_card_eq_two P C (hshape C).2
    exact ⟨l, (hshape C).1, hinterval⟩
  have hvertexBound : ∀ v : V, G.dist w v ≤ P.length :=
    IsGeodesic.rootDist_le_length_of_componentShapes
      hconn color hP hcomponentShape
  have hallAnchors (v : V) :=
    IsGeodesic.allSingletonSpanTwo_twoSidedAnchors
      (v := v) hconn hP hshape
  have haligned : ∀ i,
      G.dist (m₁ i) (m₂ i) =
        Nat.dist (G.dist w (m₁ i)) (G.dist w (m₂ i)) := by
    intro i
    exact IsGeodesic.levelAligned_of_twoSidedAnchors
      hconn hP
      (hallAnchors (m₁ i)).1 (hallAnchors (m₁ i)).2
      (hallAnchors (m₂ i)).1 (hallAnchors (m₂ i)).2
      (hvertexBound (m₁ i)) (hvertexBound (m₂ i))
      (Coloring.even_natDist_rootLevels_of_eq
        hconn color w (hsame i))
      (hlegal i)
  let extra : ℕ → ℕ := fun k =>
    (offLevelFiber P (G.dist w) k).card
  let leftExtra : Fin P.length → ℕ := fun r => extra r.1
  let rightExtra : Fin P.length → ℕ := fun r => extra (r.1 + 1)
  have hmultiplicity (r : ℕ) :
      coverMultiplicity components interval r =
        extra r + extra (r + 1) := by
    simpa [components, interval, extra] using
      IsGeodesic.coverMultiplicity_eq_adjacent_offLevelFiber_cards
        hconn hP hshape r
  have hsubset : ∀ C ∈ components,
      interval C ⊆ Finset.range P.length := by
    intro C _ r hr
    exact offCorridorComponentIntervalEdges_subset_range P C hr
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
  have hcardComponents : components.card = slack P := by
    calc
      components.card = ∑ _C ∈ components, 1 := by simp
      _ = ∑ C ∈ components, size C := by
        apply Finset.sum_congr rfl
        intro C _
        exact (hshape C).1.symm
      _ = slack P := hmass
  have hsumMultiplicity :
      (∑ r ∈ Finset.range P.length,
        coverMultiplicity components interval r) =
        ∑ C ∈ components, (interval C).card :=
    sum_coverMultiplicity_eq_sum_card
      components interval (Finset.range P.length) hsubset
  have hweightRaw :
      (∑ r ∈ Finset.range P.length,
        (extra r + extra (r + 1))) = 2 * slack P := by
    calc
      (∑ r ∈ Finset.range P.length,
          (extra r + extra (r + 1))) =
          ∑ r ∈ Finset.range P.length,
            coverMultiplicity components interval r := by
        apply Finset.sum_congr rfl
        intro r _
        exact (hmultiplicity r).symm
      _ = ∑ C ∈ components, (interval C).card := hsumMultiplicity
      _ = ∑ _C ∈ components, 2 := by
        apply Finset.sum_congr rfl
        intro C _
        simpa [interval] using (hshape C).2
      _ = 2 * slack P := by simp [hcardComponents, mul_comm]
  obtain ⟨j, hj, k, hk, hjk, hjTwo, hkTwo, hbaseline⟩ :=
    canonical_pureOverlap_two_double_coordinates
      P components hunion hpureLength
  have hMultiplicityLe (r : ℕ) (hr : r ∈ Finset.range P.length) :
      coverMultiplicity components interval r ≤ 2 := by
    by_cases hrj : r = j
    · subst r
      simpa [interval] using hjTwo.le
    · by_cases hrk : r = k
      · subst r
        simpa [interval] using hkTwo.le
      · have h := hbaseline r hr hrj hrk
        have hEq : coverMultiplicity components interval r = 1 := by
          simpa [interval] using h
        omega
  have hpositive := coverMultiplicity_pos_of_biUnion_eq
    components interval (Finset.range P.length) hunion
  have hproductPoint (r : ℕ) (hr : r ∈ Finset.range P.length) :
      extra r * extra (r + 1) ≤
        coverMultiplicity components interval r - 1 := by
    have hEq := hmultiplicity r
    have hLe := hMultiplicityLe r hr
    have hPos := hpositive r hr
    have hleft : extra r ≤ 2 := by omega
    have hright : extra (r + 1) ≤ 2 := by omega
    interval_cases extra r <;>
      interval_cases extra (r + 1) <;> omega
  have hoverlapTwo : overlapDefect components
      (fun C => (interval C).card) P.length = 2 := by
    have h := hpure.2.2.1
    rw [← hunionCard]
    simpa [span] using h
  have hpredSum :
      (∑ r ∈ Finset.range P.length,
        (coverMultiplicity components interval r - 1)) = 2 := by
    rw [← overlapDefect_eq_sum_multiplicityPred
      components interval (Finset.range P.length) hunion hsubset]
    simpa using hoverlapTwo
  have hproductRaw :
      (∑ r ∈ Finset.range P.length,
        extra r * extra (r + 1)) ≤ 2 := by
    calc
      (∑ r ∈ Finset.range P.length,
          extra r * extra (r + 1)) ≤
          ∑ r ∈ Finset.range P.length,
            (coverMultiplicity components interval r - 1) := by
        exact Finset.sum_le_sum fun r hr => hproductPoint r hr
      _ = 2 := hpredSum
  have hweightFin :
      (∑ r : Fin P.length, (leftExtra r + rightExtra r)) =
        ∑ r ∈ Finset.range P.length,
          (extra r + extra (r + 1)) := by
    simpa [leftExtra, rightExtra] using
      Fin.sum_univ_eq_sum_range
        (fun r => extra r + extra (r + 1)) P.length
  have hproductFin :
      (∑ r : Fin P.length, leftExtra r * rightExtra r) =
        ∑ r ∈ Finset.range P.length,
          extra r * extra (r + 1) := by
    simpa [leftExtra, rightExtra] using
      Fin.sum_univ_eq_sum_range
        (fun r => extra r * extra (r + 1)) P.length
  have hweight :
      (∑ r : Fin P.length, (leftExtra r + rightExtra r)) ≤
        2 * slack P := by
    rw [hweightFin, hweightRaw]
  have hadjacent :
      (∑ r : Fin P.length, leftExtra r * rightExtra r) ≤ 2 := by
    rw [hproductFin]
    exact hproductRaw
  have hstep : ∀ {u v : V}, G.Adj u v →
      Nat.dist (G.dist w u) (G.dist w v) = 1 := by
    intro u v huv
    exact Coloring.adj_rootDist_natDist_eq_one hconn color huv
  have hlayer (q : ℕ) (hq : q ≤ P.length) :
      (levelLayer (G.dist w) q).card = extra q + 1 := by
    simpa [extra, Nat.add_comm] using
      IsGeodesic.levelLayer_card_eq_one_add_offLevelFiber_card
        hP hq
  have hroot : G.dist w w = 0 := by simp
  have hstub : G.dist w x₀ = P.length := by simpa using hP.symm
  have hresult := totalCost_le_rlBudget_of_nearBoundary_adjacentExtras
    w x₀ m₁ m₂ (G.dist w) (slack P) P.length
    leftExtra rightExtra (by omega) (Or.inr htwo)
    hweight hadjacent hstep
    (fun r => hlayer r.1 (by omega))
    (fun r => hlayer (r.1 + 1) (by omega))
    hroot hstub
    (fun i => hvertexBound (m₁ i))
    (fun i => hvertexBound (m₂ i))
    haligned hRFC hlegal
  simpa [htwo] using hresult

/-- Every neighbor of the right vertex of a saturated span-three pair is
the other component vertex or one of the two corridor vertices on the
adjacent rooted levels. -/
theorem IsGeodesic.pairSpanThree_cR_neighbor_classifier
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ cL cR y : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (color : G.Coloring Bool) (hP : IsGeodesic P)
    (Cstar : OffCorridorComponent P) (a : ℕ)
    (hstar : offCorridorComponentFinset Cstar = {cL, cR})
    (hlevelR : G.dist w cR = a + 2)
    (hcy : G.Adj cR y) :
    y = cL ∨ y = P.getVert (a + 1) ∨ y = P.getVert (a + 3) := by
  classical
  have hcRStar : cR ∈ offCorridorComponentFinset Cstar := by simp [hstar]
  have hcROff : cR ∈ offCorridorFinset P :=
    mem_offCorridorFinset_of_mem_componentFinset hcRStar
  have hcRNot : cR ∉ P.support := by
    have h := (Finset.mem_sdiff.mp hcROff).2
    simpa [supportFinset] using h
  by_cases hySupport : y ∈ P.support
  · let j := P.support.idxOf y
    have hjBound : j ≤ P.length := support_idxOf_le_length P hySupport
    have hjGet : P.getVert j = y := P.getVert_support_idxOf hySupport
    have hjLevel : G.dist w y = j := by
      rw [← hjGet]
      exact IsGeodesic.rootDist_getVert hP hjBound
    have hstep := Coloring.adj_rootDist_natDist_eq_one
      (w := w) hconn color hcy
    rw [hlevelR, hjLevel] at hstep
    unfold Nat.dist at hstep
    have hj : j = a + 1 ∨ j = a + 3 := by omega
    rcases hj with hj | hj
    · right; left
      calc
        y = P.getVert j := hjGet.symm
        _ = P.getVert (a + 1) := by rw [hj]
    · right; right
      calc
        y = P.getVert j := hjGet.symm
        _ = P.getVert (a + 3) := by rw [hj]
  · have hcomp := offCorridorComponentOf_eq_of_adj
      P hcRNot hySupport hcy
    have hcRComp : cR ∈ Cstar :=
      (mem_offCorridorComponentFinset Cstar).1 hcRStar
    obtain ⟨_hcROffSet, hcREq⟩ := ComponentCompl.mem_supp_iff.mp hcRComp
    have hcROwn : offCorridorComponentOf P cR hcRNot = Cstar := by
      simpa [offCorridorComponentOf, supportFinset] using hcREq
    have hyOwn := mem_offCorridorComponentOf P hySupport
    have hyStar : y ∈ offCorridorComponentFinset Cstar := by
      simpa [← hcROwn, hcomp] using hyOwn
    have hyCases : y = cL ∨ y = cR := by simpa [hstar] using hyStar
    rcases hyCases with hy | hy
    · exact Or.inl hy
    · subst y
      exact (G.loopless.irrefl cR hcy).elim

/-- Symmetric neighbor classifier for the left vertex of a saturated
span-three pair. -/
theorem IsGeodesic.pairSpanThree_cL_neighbor_classifier
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ cL cR y : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (color : G.Coloring Bool) (hP : IsGeodesic P)
    (Cstar : OffCorridorComponent P) (a : ℕ)
    (hstar : offCorridorComponentFinset Cstar = {cL, cR})
    (hlevelL : G.dist w cL = a + 1)
    (hcy : G.Adj cL y) :
    y = cR ∨ y = P.getVert a ∨ y = P.getVert (a + 2) := by
  classical
  have hcLStar : cL ∈ offCorridorComponentFinset Cstar := by simp [hstar]
  have hcLOff : cL ∈ offCorridorFinset P :=
    mem_offCorridorFinset_of_mem_componentFinset hcLStar
  have hcLNot : cL ∉ P.support := by
    have h := (Finset.mem_sdiff.mp hcLOff).2
    simpa [supportFinset] using h
  by_cases hySupport : y ∈ P.support
  · let j := P.support.idxOf y
    have hjBound : j ≤ P.length := support_idxOf_le_length P hySupport
    have hjGet : P.getVert j = y := P.getVert_support_idxOf hySupport
    have hjLevel : G.dist w y = j := by
      rw [← hjGet]
      exact IsGeodesic.rootDist_getVert hP hjBound
    have hstep := Coloring.adj_rootDist_natDist_eq_one
      (w := w) hconn color hcy
    rw [hlevelL, hjLevel] at hstep
    unfold Nat.dist at hstep
    have hj : j = a ∨ j = a + 2 := by omega
    rcases hj with hj | hj
    · right; left
      calc
        y = P.getVert j := hjGet.symm
        _ = P.getVert a := by rw [hj]
    · right; right
      calc
        y = P.getVert j := hjGet.symm
        _ = P.getVert (a + 2) := by rw [hj]
  · have hcomp := offCorridorComponentOf_eq_of_adj
      P hcLNot hySupport hcy
    have hcLComp : cL ∈ Cstar :=
      (mem_offCorridorComponentFinset Cstar).1 hcLStar
    obtain ⟨_hcLOffSet, hcLEq⟩ := ComponentCompl.mem_supp_iff.mp hcLComp
    have hcLOwn : offCorridorComponentOf P cL hcLNot = Cstar := by
      simpa [offCorridorComponentOf, supportFinset] using hcLEq
    have hyOwn := mem_offCorridorComponentOf P hySupport
    have hyStar : y ∈ offCorridorComponentFinset Cstar := by
      simpa [← hcLOwn, hcomp] using hyOwn
    have hyCases : y = cL ∨ y = cR := by simpa [hstar] using hyStar
    rcases hyCases with hy | hy
    · subst y
      exact (G.loopless.irrefl cL hcy).elim
    · exact Or.inl hy

/-- A singleton span-two component has no neighbors except its two extreme
corridor attachment vertices. -/
theorem IsGeodesic.singletonSpanTwo_neighbor_classifier
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ c y : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (color : G.Coloring Bool) (hP : IsGeodesic P)
    (C : OffCorridorComponent P) (l : ℕ)
    (hset : offCorridorComponentFinset C = {c})
    (hinterval : offCorridorComponentIntervalEdges P C =
      Finset.Ico l (l + 2))
    (hcy : G.Adj c y) :
    y = P.getVert l ∨ y = P.getVert (l + 2) := by
  classical
  have hcLevel := IsGeodesic.rootDist_singleton_spanTwo
    hconn hP C c l hset hinterval
  have hcC : c ∈ offCorridorComponentFinset C := by simp [hset]
  have hcOff : c ∈ offCorridorFinset P :=
    mem_offCorridorFinset_of_mem_componentFinset hcC
  have hcNot : c ∉ P.support := by
    have h := (Finset.mem_sdiff.mp hcOff).2
    simpa [supportFinset] using h
  by_cases hySupport : y ∈ P.support
  · let j := P.support.idxOf y
    have hjBound : j ≤ P.length := support_idxOf_le_length P hySupport
    have hjGet : P.getVert j = y := P.getVert_support_idxOf hySupport
    have hjLevel : G.dist w y = j := by
      rw [← hjGet]
      exact IsGeodesic.rootDist_getVert hP hjBound
    have hstep := Coloring.adj_rootDist_natDist_eq_one
      (w := w) hconn color hcy
    rw [hcLevel, hjLevel] at hstep
    unfold Nat.dist at hstep
    have hj : j = l ∨ j = l + 2 := by omega
    rcases hj with hj | hj
    · left
      calc
        y = P.getVert j := hjGet.symm
        _ = P.getVert l := by rw [hj]
    · right
      calc
        y = P.getVert j := hjGet.symm
        _ = P.getVert (l + 2) := by rw [hj]
  · have hcomp := offCorridorComponentOf_eq_of_adj P hcNot hySupport hcy
    have hcComp : c ∈ C := (mem_offCorridorComponentFinset C).1 hcC
    obtain ⟨_hcOffSet, hcEq⟩ := ComponentCompl.mem_supp_iff.mp hcComp
    have hcOwn : offCorridorComponentOf P c hcNot = C := by
      simpa [offCorridorComponentOf, supportFinset] using hcEq
    have hyOwn := mem_offCorridorComponentOf P hySupport
    have hyC : y ∈ offCorridorComponentFinset C := by
      simpa [← hcOwn, hcomp] using hyOwn
    have hyc : y = c := by simpa [hset] using hyC
    subst y
    exact (G.loopless.irrefl c hcy).elim

/-- If the optional inner chord at the right contact is absent, the right
pair vertex has only the internal edge and the far corridor attachment. -/
theorem IsGeodesic.pairSpanThree_cR_neighbor_classifier_of_no_innerChord
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ cL cR : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (color : G.Coloring Bool) (hP : IsGeodesic P)
    (Cstar : OffCorridorComponent P) (a : ℕ)
    (hstar : offCorridorComponentFinset Cstar = {cL, cR})
    (hlevelR : G.dist w cR = a + 2)
    (hno : ¬G.Adj cR (P.getVert (a + 1))) :
    ∀ y, G.Adj cR y → y = cL ∨ y = P.getVert (a + 3) := by
  intro y hcy
  rcases IsGeodesic.pairSpanThree_cR_neighbor_classifier
    hconn color hP Cstar a hstar hlevelR hcy with hy | hy | hy
  · exact Or.inl hy
  · subst y
    exact (hno hcy).elim
  · exact Or.inr hy

/-- A regular off-corridor vertex at level `a+3` is the singleton midpoint
of the block `[a+2,a+4)`.  In particular the far endpoint is in range and
the vertex has exactly the two extreme corridor neighbors. -/
theorem IsGeodesic.massOverlap_regular_level_add_three_geometry
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ z cL cR : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (color : G.Coloring Bool) (hP : IsGeodesic P)
    (Cstar : OffCorridorComponent P) (a : ℕ)
    (hstar : offCorridorComponentFinset Cstar = {cL, cR})
    (hothers : ∀ C : OffCorridorComponent P, C ≠ Cstar →
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2)
    (hzOff : z ∈ offCorridorFinset P)
    (hzL : z ≠ cL) (hzR : z ≠ cR)
    (hzLevel : G.dist w z = a + 3) :
    ∃ C : OffCorridorComponent P,
      C ≠ Cstar ∧
      offCorridorComponentFinset C = {z} ∧
      offCorridorComponentIntervalEdges P C =
        Finset.Ico (a + 2) (a + 4) ∧
      a + 4 ≤ P.length ∧
      G.neighborFinset z = {P.getVert (a + 2), P.getVert (a + 4)} := by
  classical
  have hzNot : z ∉ P.support := by
    have h := (Finset.mem_sdiff.mp hzOff).2
    simpa [supportFinset] using h
  let C := offCorridorComponentOf P z hzNot
  have hzC : z ∈ offCorridorComponentFinset C :=
    mem_offCorridorComponentOf P hzNot
  have hCne : C ≠ Cstar := by
    intro hEq
    have hzStar : z ∈ offCorridorComponentFinset Cstar := by
      simpa [hEq] using hzC
    have hzCases : z = cL ∨ z = cR := by simpa [hstar] using hzStar
    exact hzCases.elim hzL hzR
  obtain ⟨hsize, hspan⟩ := hothers C hCne
  obtain ⟨l, hinterval⟩ :=
    offCorridorInterval_eq_Ico_of_card_eq_two P C hspan
  obtain ⟨c, hset, hcLevel, hleft, hright⟩ :=
    IsGeodesic.singleton_spanTwo_geometry
      hconn hP C l hsize hinterval
  have hzc : z = c := by simpa [hset] using hzC
  subst c
  have hl : l = a + 2 := by omega
  subst l
  have hfar : a + 4 ≤ P.length := by
    have hmem : a + 3 ∈ offCorridorComponentIntervalEdges P C := by
      rw [hinterval]
      simp
    have hrange := offCorridorComponentIntervalEdges_subset_range P C hmem
    have hlt := Finset.mem_range.mp hrange
    omega
  have hneighbors :
      G.neighborFinset z = {P.getVert (a + 2), P.getVert (a + 4)} := by
    ext y
    constructor
    · intro hy
      have hzy : G.Adj z y := by simpa using hy
      rcases IsGeodesic.singletonSpanTwo_neighbor_classifier
        hconn color hP C (a + 2) hset hinterval hzy with hy | hy
      · simp [hy]
      · simp [hy]
    · intro hy
      have hyCases : y = P.getVert (a + 2) ∨ y = P.getVert (a + 4) := by
        simpa using hy
      rcases hyCases with hy | hy
      · subst y
        simpa using hleft
      · subst y
        simpa using hright
  exact ⟨C, hCne, hset, hinterval, hfar, hneighbors⟩

/-- A left-contact row has rooted span two and graph distance at most four. -/
theorem IsGeodesic.massOverlap_leftContact_distance
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ cL cR z : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P)
    (Cstar : OffCorridorComponent P) (a : ℕ)
    (hstar : offCorridorComponentFinset Cstar = {cL, cR})
    (hothers : ∀ C : OffCorridorComponent P, C ≠ Cstar →
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2)
    (hLR : G.Adj cL cR)
    (hleft : G.Adj cL (P.getVert a))
    (hlevelL : G.dist w cL = a + 1)
    (hlevelR : G.dist w cR = a + 2)
    (hlength : a + 3 ≤ P.length)
    (hzOff : z ∈ offCorridorFinset P)
    (hzLevel : G.dist w z = a) :
    G.dist cR z ≤ Nat.dist (G.dist w cR) (G.dist w z) + 2 ∧
      Nat.dist (G.dist w cR) (G.dist w z) = 2 := by
  have hzL : z ≠ cL := by intro h; subst z; omega
  have hzR : z ≠ cR := by intro h; subst z; omega
  have hzNext :=
    (IsGeodesic.massOverlap_regular_twoSidedAnchors
      (v := z) hconn hP Cstar hstar hothers hzL hzR).1 (by omega)
  have hzP : G.Adj z (P.getVert (a + 1)) := by
    simpa [hzLevel] using hzNext
  have hpEdge := P.adj_getVert_succ (i := a) (by omega)
  have hRLdist : G.dist cR cL = 1 := dist_eq_one_iff_adj.mpr hLR.symm
  have hLp : G.dist cL (P.getVert a) = 1 := dist_eq_one_iff_adj.mpr hleft
  have hpp : G.dist (P.getVert a) (P.getVert (a + 1)) = 1 :=
    dist_eq_one_iff_adj.mpr hpEdge
  have hpz : G.dist (P.getVert (a + 1)) z = 1 :=
    dist_eq_one_iff_adj.mpr hzP.symm
  have htri₁ := hconn.dist_triangle
    (u := cR) (v := cL) (w := P.getVert a)
  have htri₂ := hconn.dist_triangle
    (u := cR) (v := P.getVert a) (w := P.getVert (a + 1))
  have htri₃ := hconn.dist_triangle
    (u := cR) (v := P.getVert (a + 1)) (w := z)
  have hnat : Nat.dist (G.dist w cR) (G.dist w z) = 2 := by
    rw [hlevelR, hzLevel, Nat.dist_eq_sub_of_le_right (by omega)]
    omega
  constructor
  · omega
  · exact hnat

/-- A right-contact row has rooted span two and graph distance at most four. -/
theorem IsGeodesic.massOverlap_rightContact_distance
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ cL cR z : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P)
    (Cstar : OffCorridorComponent P) (a : ℕ)
    (hstar : offCorridorComponentFinset Cstar = {cL, cR})
    (hothers : ∀ C : OffCorridorComponent P, C ≠ Cstar →
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2)
    (hLR : G.Adj cL cR)
    (hright : G.Adj cR (P.getVert (a + 3)))
    (hlevelL : G.dist w cL = a + 1)
    (hlevelR : G.dist w cR = a + 2)
    (hlength : a + 3 ≤ P.length)
    (hzOff : z ∈ offCorridorFinset P)
    (hzLevel : G.dist w z = a + 3) :
    G.dist cL z ≤ Nat.dist (G.dist w cL) (G.dist w z) + 2 ∧
      Nat.dist (G.dist w cL) (G.dist w z) = 2 := by
  have hzL : z ≠ cL := by intro h; subst z; omega
  have hzR : z ≠ cR := by intro h; subst z; omega
  have hzPrev :=
    (IsGeodesic.massOverlap_regular_twoSidedAnchors
      (v := z) hconn hP Cstar hstar hothers hzL hzR).2 (by omega)
  have hpZ : G.Adj (P.getVert (a + 2)) z := by
    simpa [hzLevel] using hzPrev
  have hpEdge := P.adj_getVert_succ (i := a + 2) (by omega)
  have hLRdist : G.dist cL cR = 1 := dist_eq_one_iff_adj.mpr hLR
  have hRp : G.dist cR (P.getVert (a + 3)) = 1 :=
    dist_eq_one_iff_adj.mpr hright
  have hpp : G.dist (P.getVert (a + 3)) (P.getVert (a + 2)) = 1 :=
    dist_eq_one_iff_adj.mpr hpEdge.symm
  have hpz : G.dist (P.getVert (a + 2)) z = 1 :=
    dist_eq_one_iff_adj.mpr hpZ
  have htri₁ := hconn.dist_triangle
    (u := cL) (v := cR) (w := P.getVert (a + 3))
  have htri₂ := hconn.dist_triangle
    (u := cL) (v := P.getVert (a + 3)) (w := P.getVert (a + 2))
  have htri₃ := hconn.dist_triangle
    (u := cL) (v := P.getVert (a + 2)) (w := z)
  have hnat : Nat.dist (G.dist w cL) (G.dist w z) = 2 := by
    rw [hlevelL, hzLevel, Nat.dist_eq_sub_of_le (by omega)]
    omega
  constructor
  · omega
  · exact hnat

/-- Threshold-cut landing when the supplied exceptional predicate contains
at most one demand.  If it is empty, use the aligned near-boundary profile;
if it is inhabited, use the one-row `+2` envelope at its unique member. -/
theorem totalCost_le_rlBudget_of_zeroOrOne_addTwo_levelCuts
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (w x₀ : V) (m₁ m₂ : I → V) (level : V → ℕ)
    (s d : ℕ) (capacity weight : Fin d → ℕ)
    (exceptional : I → Prop) [DecidablePred exceptional]
    (hs : 4 ≤ s) (hrow : d = 2 * s - 1 ∨ d = 2 * s - 2)
    (hcapacity : ∀ r, capacity r ≤ (weight r) ^ 2)
    (hweight : (∑ r : Fin d, weight r) ≤ 2 * s)
    (hcapacitySum : (∑ r : Fin d, capacity r) ≤ 2 * s + 2)
    (hroot : level w = 0) (hstub : level x₀ = d)
    (hendpoint₁ : ∀ i, level (m₁ i) ≤ d)
    (hendpoint₂ : ∀ i, level (m₂ i) ≤ d)
    (haligned : ∀ i, ¬ exceptional i →
      G.dist (m₁ i) (m₂ i) =
        Nat.dist (level (m₁ i)) (level (m₂ i)))
    (hexceptional : ∀ i, exceptional i →
      G.dist (m₁ i) (m₂ i) ≤
        Nat.dist (level (m₁ i)) (level (m₂ i)) + 2)
    (hcard : ((Finset.univ : Finset I).filter exceptional).card ≤ 1)
    (hRFC : ∀ T : Finset V, w ∉ T →
      (∑ i : I, separationDemand T (m₁ i) (m₂ i)) +
        (if x₀ ∈ T then 1 else 0) ≤ cutSize G T)
    (hcut : ∀ r : Fin d,
      cutSize G (levelUpperCut level r.1) ≤ capacity r + 1)
    (hlegal : ∀ i, 4 ≤ G.dist (m₁ i) (m₂ i))
    (henvelope : ∀ i, exceptional i →
      let Q := ∑ r : Fin d, ∑ q : Fin d, min (capacity r) (capacity q)
      let C := ∑ r : Fin d, capacity r
      let L := Nat.dist (level (m₁ i)) (level (m₂ i))
      4 * Q + 9 * C + 16 * L + 34 ≤ 4 * rlBudget s d) :
    (∑ i : I, (G.dist (m₁ i) (m₂ i) + 1) ^ 2) ≤
      rlBudget s d := by
  classical
  let E : Finset I := (Finset.univ : Finset I).filter exceptional
  by_cases hE : E = ∅
  · exact totalCost_le_rlBudget_of_nearBoundaryCapacityProfile
      w x₀ m₁ m₂ level s d capacity weight hs hrow hcapacity
      hweight hcapacitySum hroot hstub hendpoint₁ hendpoint₂
      (fun i ↦ haligned i (by
        intro hi
        have hiE : i ∈ E := by simp [E, hi]
        have hiNotE : i ∉ E := by simp [hE]
        exact hiNotE hiE))
      hRFC hcut hlegal
  · obtain ⟨e, heE⟩ := Finset.nonempty_iff_ne_empty.mpr hE
    have he : exceptional e := (Finset.mem_filter.mp heE).2
    exact totalCost_le_rlBudget_of_one_addTwo_levelCuts
      w x₀ m₁ m₂ level s d capacity e hroot hstub
      hendpoint₁ hendpoint₂
      (fun i hie ↦ haligned i (by
        intro hi
        have hiE : i ∈ E := by simp [E, hi]
        have hie' : i = e := (Finset.card_le_one.mp hcard) i hiE e heE
        exact hie hie'))
      (hexceptional e he) hRFC hcut hlegal (henvelope e he)


set_option maxHeartbeats 3000000 in
/-- Complete mixed mass-overlap closure on the two-defect row. -/
theorem totalCost_le_rlBudget_of_massOverlap_allNonbridge_sameSide
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
    (hmixed :
      let components := (Finset.univ : Finset (OffCorridorComponent P))
      let size : OffCorridorComponent P → ℕ := fun C =>
        (offCorridorComponentFinset C).card
      let span : OffCorridorComponent P → ℕ := fun C =>
        (offCorridorComponentIntervalEdges P C).card
      let unionCard :=
        (components.biUnion (offCorridorComponentIntervalEdges P)).card
      MassOverlapShape components size span (slack P) unionCard)
    (hRFC : ∀ T : Finset V, w ∉ T →
      (∑ i : I, separationDemand T (m₁ i) (m₂ i)) +
        (if x₀ ∈ T then 1 else 0) ≤ cutSize G T)
    (hs : 5 ≤ slack P)
    (hlegal : ∀ i, 4 ≤ G.dist (m₁ i) (m₂ i))
    (hsame : ∀ i, color (m₁ i) = color (m₂ i)) :
    (∑ i : I, (G.dist (m₁ i) (m₂ i) + 1) ^ 2) ≤
      rlBudget (slack P) (2 * slack P - 2) := by
  classical
  obtain ⟨Cstar, a, cL, cR, j, hstar, hne, hLR, hleft, hright,
      hlevelL, hlevelR, hstarInterval, hothers, hjRange, hjTwo,
      hbase, hjne⟩ :=
    IsGeodesic.massOverlap_namedProfile hconn color hP hnonbridge hmixed
  have hstarSize : (offCorridorComponentFinset Cstar).card = 2 := by
    rw [hstar]
    simp [hne]
  have haStar : a ∈ offCorridorComponentIntervalEdges P Cstar := by
    rw [hstarInterval]
    simp
  have haTwoStar : a + 2 ∈ offCorridorComponentIntervalEdges P Cstar := by
    rw [hstarInterval]
    simp
  have haRange : a ∈ Finset.range P.length :=
    offCorridorComponentIntervalEdges_subset_range P Cstar haStar
  have haTwoRange : a + 2 ∈ Finset.range P.length :=
    offCorridorComponentIntervalEdges_subset_range P Cstar haTwoStar
  have hlength : a + 3 ≤ P.length := by
    have := Finset.mem_range.mp haTwoRange
    omega
  have hcomponentShape : ∀ C : OffCorridorComponent P,
      hasOneDefectShape P C := by
    intro C
    by_cases hC : C = Cstar
    · subst C
      right
      exact ⟨a, hstarSize, hstarInterval⟩
    · left
      obtain ⟨l, hinterval⟩ :=
        offCorridorInterval_eq_Ico_of_card_eq_two P C (hothers C hC).2
      exact ⟨l, (hothers C hC).1, hinterval⟩
  have hvertexBound : ∀ v : V, G.dist w v ≤ P.length :=
    IsGeodesic.rootDist_le_length_of_componentShapes
      hconn color hP hcomponentShape
  have hcLStar : cL ∈ offCorridorComponentFinset Cstar := by simp [hstar]
  have hcRStar : cR ∈ offCorridorComponentFinset Cstar := by simp [hstar]
  have hcLOff : cL ∈ offCorridorFinset P :=
    mem_offCorridorFinset_of_mem_componentFinset hcLStar
  have hcROff : cR ∈ offCorridorFinset P :=
    mem_offCorridorFinset_of_mem_componentFinset hcRStar
  have hinjective : Set.InjOn (G.dist w) (offCorridorFinset P : Set V) :=
    IsGeodesic.massOverlap_rootDist_injective_of_uniqueDouble
      hconn hP Cstar a j hstar hlevelL hlevelR hstarInterval hothers hbase
  have hbinary (k : ℕ) :
      (offLevelFiber P (G.dist w) k).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    have hxData := Finset.mem_filter.mp hx
    have hyData := Finset.mem_filter.mp hy
    exact hinjective hxData.1 hyData.1 (hxData.2.trans hyData.2.symm)
  let extra : ℕ → ℕ := fun k =>
    (offLevelFiber P (G.dist w) k).card
  let weight : Fin P.length → ℕ := fun r =>
    extra r.1 + extra (r.1 + 1)
  let capacity : Fin P.length → ℕ := fun r =>
    weight r + extra r.1 * extra (r.1 + 1)
  obtain ⟨highFin, hhighCard, hhighMem, hweightProfile, hweightSum,
      hproductSum, hcapacitySq, hcapacityProfile, hcapacitySum, hQ⟩ :=
    IsGeodesic.massOverlap_twoHighCapacityProfile
      hconn color hP htwo hs Cstar a j hstarSize hstarInterval hothers
      hjRange hjTwo hbase hjne hbinary
  have hstep : ∀ {u v : V}, G.Adj u v →
      Nat.dist (G.dist w u) (G.dist w v) = 1 := by
    intro u v huv
    exact Coloring.adj_rootDist_natDist_eq_one hconn color huv
  have hlayer (q : ℕ) (hq : q ≤ P.length) :
      (levelLayer (G.dist w) q).card = extra q + 1 := by
    simpa [extra, Nat.add_comm] using
      IsGeodesic.levelLayer_card_eq_one_add_offLevelFiber_card hP hq
  have hcut : ∀ r : Fin P.length,
      cutSize G (levelUpperCut (G.dist w) r.1) ≤ capacity r + 1 := by
    intro r
    have hproduct := cutSize_levelUpperCut_le_layerProduct
      (G.dist w) hstep r.1
    rw [hlayer r.1 (by omega), hlayer (r.1 + 1) (by omega)] at hproduct
    dsimp [capacity, weight]
    nlinarith
  have hroot : G.dist w w = 0 := by simp
  have hstub : G.dist w x₀ = P.length := by simpa using hP.symm
  have hleftForces : ∀ z : V, z ∈ offCorridorFinset P →
      G.dist w z = a → j = a := by
    intro z hzOff hzLevel
    have hzL : z ≠ cL := by intro h; subst z; omega
    have hzR : z ≠ cR := by intro h; subst z; omega
    exact IsGeodesic.massOverlap_doubleCoordinate_eq_of_contactLevel
      hconn hP Cstar a j a hstar hstarInterval hothers hbase
      haRange haStar hzOff hzL hzR (Or.inl hzLevel)
  have hrightForces : ∀ z : V, z ∈ offCorridorFinset P →
      G.dist w z = a + 3 → j = a + 2 := by
    intro z hzOff hzLevel
    have hzL : z ≠ cL := by intro h; subst z; omega
    have hzR : z ≠ cR := by intro h; subst z; omega
    exact IsGeodesic.massOverlap_doubleCoordinate_eq_of_contactLevel
      hconn hP Cstar a j (a + 2) hstar hstarInterval hothers hbase
      haTwoRange haTwoStar hzOff hzL hzR (Or.inr (by omega))
  have hclass (i : I) :=
    IsGeodesic.massOverlap_levelAligned_or_contact
      hconn hP Cstar a hstar hothers hLR hleft hright hlevelL hlevelR
      hlength (hvertexBound (m₁ i)) (hvertexBound (m₂ i))
      (Coloring.even_natDist_rootLevels_of_eq hconn color w (hsame i))
      (hlegal i)
  let exceptional : I → Prop := fun i =>
    G.dist (m₁ i) (m₂ i) ≠
      Nat.dist (G.dist w (m₁ i)) (G.dist w (m₂ i))
  have hlocalExceptional : ∀ i, exceptional i →
      (∃ z ∈ offCorridorFinset P,
        G.dist w z = a ∧ PairMatches (m₁ i) (m₂ i) z cR) ∨
      (∃ z ∈ offCorridorFinset P,
        G.dist w z = a + 3 ∧ PairMatches (m₁ i) (m₂ i) cL z) := by
    intro i hi
    rcases hclass i with haligned | hcontact
    · exact (hi haligned).elim
    · exact hcontact
  have hcontactBounds : ∀ i, exceptional i →
      G.dist (m₁ i) (m₂ i) ≤
        Nat.dist (G.dist w (m₁ i)) (G.dist w (m₂ i)) + 2 ∧
      Nat.dist (G.dist w (m₁ i)) (G.dist w (m₂ i)) = 2 := by
    intro i hi
    rcases hlocalExceptional i hi with
      ⟨z, hzOff, hzLevel, hmatch⟩ | ⟨z, hzOff, hzLevel, hmatch⟩
    · have hdist := IsGeodesic.massOverlap_leftContact_distance
        hconn hP Cstar a hstar hothers hLR hleft hlevelL hlevelR
        hlength hzOff hzLevel
      rcases hmatch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simpa [SimpleGraph.dist_comm, Nat.dist_comm] using hdist
      · exact hdist
    · have hdist := IsGeodesic.massOverlap_rightContact_distance
        hconn hP Cstar a hstar hothers hLR hright hlevelL hlevelR
        hlength hzOff hzLevel
      rcases hmatch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hdist
      · simpa [SimpleGraph.dist_comm, Nat.dist_comm] using hdist
  have hleftCard : ∀ z : V, z ∈ offCorridorFinset P →
      G.dist w z = a → 4 ≤ G.dist z cR →
      ((Finset.univ : Finset I).filter exceptional).card ≤ 1 := by
    intro z hzOff hzLevel hzLegal
    have hzL : z ≠ cL := by intro h; subst z; omega
    have hzR : z ≠ cR := by intro h; subst z; omega
    have hjEq : j = a := hleftForces z hzOff hzLevel
    have hzNext :=
      (IsGeodesic.massOverlap_regular_twoSidedAnchors
        (v := z) hconn hP Cstar hstar hothers hzL hzR).1 (by omega)
    have hzP : G.Adj z (P.getVert (a + 1)) := by
      simpa [hzLevel] using hzNext
    have hnoInner : ¬G.Adj cR (P.getVert (a + 1)) := by
      intro hinner
      have hzp : G.dist z (P.getVert (a + 1)) = 1 :=
        dist_eq_one_iff_adj.mpr hzP
      have hpr : G.dist (P.getVert (a + 1)) cR = 1 :=
        dist_eq_one_iff_adj.mpr hinner.symm
      have htri := hconn.dist_triangle
        (u := z) (v := P.getVert (a + 1)) (w := cR)
      omega
    have hRfiberMem : cR ∈
        offLevelFiber P (G.dist w) (a + 2) :=
      Finset.mem_filter.mpr ⟨hcROff, hlevelR⟩
    have hRfiber : offLevelFiber P (G.dist w) (a + 2) = {cR} := by
      ext v
      constructor
      · intro hv
        have hvData := Finset.mem_filter.mp hv
        have hvcR := hinjective hvData.1 hcROff
          (hvData.2.trans hlevelR.symm)
        simp [hvcR]
      · intro hv
        have hvcR : v = cR := by simpa using hv
        simpa [hvcR] using hRfiberMem
    have haTwoOne := hbase (a + 2) haTwoRange (by rw [hjEq]; omega)
    have hsumNext :=
      IsGeodesic.coverMultiplicity_add_pairMiddle_eq_adjacent_offLevelFiber_cards
        hconn color hP Cstar a (a + 2) hstarSize hstarInterval hothers
    rw [haTwoOne, hRfiber] at hsumNext
    have hnextZero : offLevelFiber P (G.dist w) (a + 3) = ∅ := by
      apply Finset.card_eq_zero.mp
      simpa using hsumNext
    have hfiber₂ : levelLayer (G.dist w) (a + 2) =
        {P.getVert (a + 2), cR} := by
      rw [IsGeodesic.levelLayer_eq_insert_getVert_offLevelFiber
        hP (by omega), hRfiber]
    have hfiber₃ : levelLayer (G.dist w) (a + 3) =
        {P.getVert (a + 3)} := by
      rw [IsGeodesic.levelLayer_eq_insert_getVert_offLevelFiber
        hP hlength, hnextZero]
      simp
    have hneighborsR : ∀ y : V, G.Adj cR y →
        y = cL ∨ y = P.getVert (a + 3) :=
      IsGeodesic.pairSpanThree_cR_neighbor_classifier_of_no_innerChord
        hconn color hP Cstar a hstar hlevelR hnoInner
    let T := insert cR (levelUpperCut (G.dist w) (a + 2))
    have hcutTwo : cutSize G T ≤ 2 := by
      simpa [T] using cutSize_insert_rightVertex_levelUpperCut_le_two
        (G := G) (G.dist w) a (P.getVert (a + 2))
        (P.getVert (a + 3)) cR cL hstep hlevelR hlevelL
        hfiber₂ hfiber₃ hneighborsR
    have hwNeR : w ≠ cR := by intro h; subst cR; simp at hlevelR
    have hrootT : w ∉ T := by
      intro hwT
      rcases Finset.mem_insert.mp hwT with hwR | hwUpper
      · exact hwNeR hwR
      · have := (mem_levelUpperCut (G.dist w) (a + 2) w).1 hwUpper
        simp at this
    have hxT : x₀ ∈ T := by
      apply Finset.mem_insert.mpr
      right
      apply (mem_levelUpperCut (G.dist w) (a + 2) x₀).2
      rw [hstub]
      omega
    have hzT : z ∉ T := by
      intro hzMem
      rcases Finset.mem_insert.mp hzMem with hzcR | hzUpper
      · exact hzR hzcR
      · have := (mem_levelUpperCut (G.dist w) (a + 2) z).1 hzUpper
        omega
    have hcRT : cR ∈ T := Finset.mem_insert_self _ _
    have hsupported : ∀ i, exceptional i →
        Separates T (m₁ i) (m₂ i) := by
      intro i hi
      rcases hlocalExceptional i hi with
        ⟨z', hz'Off, hz'Level, hmatch⟩ |
        ⟨z', hz'Off, hz'Level, hmatch⟩
      · have hz'eq : z' = z := hinjective hz'Off hzOff
          (hz'Level.trans hzLevel.symm)
        subst z'
        rcases hmatch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp [Separates, hzT, hcRT]
      · have hjRight := hrightForces z' hz'Off hz'Level
        rw [hjEq] at hjRight
        omega
    apply rootedCutCondition_atMostOne_cutSupported_exception
      m₁ m₂ w x₀ hRFC T exceptional hrootT
    · simp [hxT]
      exact hcutTwo
    · exact hsupported
  have hrightCard : ∀ z : V, z ∈ offCorridorFinset P →
      G.dist w z = a + 3 → 4 ≤ G.dist cL z →
      ((Finset.univ : Finset I).filter exceptional).card ≤ 1 := by
    intro z hzOff hzLevel hzLegal
    have hzL : z ≠ cL := by intro h; subst z; omega
    have hzR : z ≠ cR := by intro h; subst z; omega
    have hjEq : j = a + 2 := hrightForces z hzOff hzLevel
    obtain ⟨C, hCne, hset, hinterval, hfar, hneighborsEq⟩ :=
      IsGeodesic.massOverlap_regular_level_add_three_geometry
        hconn color hP Cstar a hstar hothers hzOff hzL hzR hzLevel
    have hzFiberMem : z ∈
        offLevelFiber P (G.dist w) (a + 3) :=
      Finset.mem_filter.mpr ⟨hzOff, hzLevel⟩
    have hzFiber : offLevelFiber P (G.dist w) (a + 3) = {z} := by
      ext v
      constructor
      · intro hv
        have hvData := Finset.mem_filter.mp hv
        have hvz := hinjective hvData.1 hzOff
          (hvData.2.trans hzLevel.symm)
        simp [hvz]
      · intro hv
        have hvz : v = z := by simpa using hv
        simpa [hvz] using hzFiberMem
    have haThreeRange : a + 3 ∈ Finset.range P.length :=
      Finset.mem_range.mpr (by omega)
    have haThreeOne := hbase (a + 3) haThreeRange (by rw [hjEq]; omega)
    have hsumNext :=
      IsGeodesic.coverMultiplicity_add_pairMiddle_eq_adjacent_offLevelFiber_cards
        hconn color hP Cstar a (a + 3) hstarSize hstarInterval hothers
    rw [haThreeOne, hzFiber] at hsumNext
    have hnextZero : offLevelFiber P (G.dist w) (a + 4) = ∅ := by
      apply Finset.card_eq_zero.mp
      simpa using hsumNext
    have hfiber₃ : levelLayer (G.dist w) (a + 3) =
        {P.getVert (a + 3), z} := by
      rw [IsGeodesic.levelLayer_eq_insert_getVert_offLevelFiber
        hP (by omega), hzFiber]
    have hfiber₄ : levelLayer (G.dist w) (a + 4) =
        {P.getVert (a + 4)} := by
      rw [IsGeodesic.levelLayer_eq_insert_getVert_offLevelFiber
        hP hfar, hnextZero]
      simp
    have hlevelp₂ : G.dist w (P.getVert (a + 2)) = a + 2 := by
      simpa using IsGeodesic.rootDist_getVert hP (by omega)
    have hneighborsZ : ∀ y : V, G.Adj z y →
        y = P.getVert (a + 2) ∨ y = P.getVert (a + 4) := by
      intro y hzy
      have hyMem : y ∈ G.neighborFinset z := by simpa using hzy
      rw [hneighborsEq] at hyMem
      simpa using hyMem
    let T := insert z (levelUpperCut (G.dist w) (a + 3))
    have hcutTwo : cutSize G T ≤ 2 := by
      simpa [T] using cutSize_insert_singleton_levelUpperCut_le_two
        (G := G) (G.dist w) a (P.getVert (a + 2))
        (P.getVert (a + 3)) (P.getVert (a + 4)) z
        hstep hzLevel hlevelp₂ hfiber₃ hfiber₄ hneighborsZ
    have hwNeZ : w ≠ z := by intro h; subst z; simp at hzLevel
    have hrootT : w ∉ T := by
      intro hwT
      rcases Finset.mem_insert.mp hwT with hwz | hwUpper
      · exact hwNeZ hwz
      · have := (mem_levelUpperCut (G.dist w) (a + 3) w).1 hwUpper
        simp at this
    have hxT : x₀ ∈ T := by
      apply Finset.mem_insert.mpr
      right
      apply (mem_levelUpperCut (G.dist w) (a + 3) x₀).2
      rw [hstub]
      omega
    have hzT : z ∈ T := Finset.mem_insert_self _ _
    have hcLT : cL ∉ T := by
      intro hmem
      rcases Finset.mem_insert.mp hmem with hcLz | hcLUpper
      · exact hzL hcLz.symm
      · have := (mem_levelUpperCut (G.dist w) (a + 3) cL).1 hcLUpper
        omega
    have hsupported : ∀ i, exceptional i →
        Separates T (m₁ i) (m₂ i) := by
      intro i hi
      rcases hlocalExceptional i hi with
        ⟨z', hz'Off, hz'Level, hmatch⟩ |
        ⟨z', hz'Off, hz'Level, hmatch⟩
      · have hjLeft := hleftForces z' hz'Off hz'Level
        rw [hjEq] at hjLeft
        omega
      · have hz'eq : z' = z := hinjective hz'Off hzOff
          (hz'Level.trans hzLevel.symm)
        subst z'
        rcases hmatch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp [Separates, hcLT, hzT]
    apply rootedCutCondition_atMostOne_cutSupported_exception
      m₁ m₂ w x₀ hRFC T exceptional hrootT
    · simp [hxT]
      exact hcutTwo
    · exact hsupported
  have hcard :
      ((Finset.univ : Finset I).filter exceptional).card ≤ 1 := by
    let E : Finset I := (Finset.univ : Finset I).filter exceptional
    by_cases hE : E = ∅
    · change E.card ≤ 1
      simp [hE]
    · obtain ⟨e, heE⟩ := Finset.nonempty_iff_ne_empty.mpr hE
      have he : exceptional e := (Finset.mem_filter.mp heE).2
      rcases hlocalExceptional e he with
        ⟨z, hzOff, hzLevel, hmatch⟩ |
        ⟨z, hzOff, hzLevel, hmatch⟩
      · rcases hmatch with ⟨hm1, hm2⟩ | ⟨hm1, hm2⟩
        · exact hleftCard z hzOff hzLevel (by
            simpa [hm1, hm2] using hlegal e)
        · exact hleftCard z hzOff hzLevel (by
            simpa [hm1, hm2, SimpleGraph.dist_comm] using hlegal e)
      · rcases hmatch with ⟨hm1, hm2⟩ | ⟨hm1, hm2⟩
        · exact hrightCard z hzOff hzLevel (by
            simpa [hm1, hm2] using hlegal e)
        · exact hrightCard z hzOff hzLevel (by
            simpa [hm1, hm2, SimpleGraph.dist_comm] using hlegal e)
  have haligned : ∀ i, ¬exceptional i →
      G.dist (m₁ i) (m₂ i) =
        Nat.dist (G.dist w (m₁ i)) (G.dist w (m₂ i)) := by
    intro i hi
    exact not_ne_iff.mp (by simpa [exceptional] using hi)
  have hexceptional : ∀ i, exceptional i →
      G.dist (m₁ i) (m₂ i) ≤
        Nat.dist (G.dist w (m₁ i)) (G.dist w (m₂ i)) + 2 := by
    intro i hi
    exact (hcontactBounds i hi).1
  have hspanBound : ∀ i, exceptional i →
      Nat.dist (G.dist w (m₁ i)) (G.dist w (m₂ i)) ≤
        P.length - 2 := by
    intro i hi
    rw [(hcontactBounds i hi).2]
    rw [htwo]
    omega
  have hprofileBounds := twoHighColumns_fin_profile_bounds
    P.length capacity highFin hhighCard.le hcapacityProfile
  have henvelope : ∀ i, exceptional i →
      let Q := ∑ r : Fin P.length, ∑ q : Fin P.length,
        min (capacity r) (capacity q)
      let C := ∑ r : Fin P.length, capacity r
      let L := Nat.dist (G.dist w (m₁ i)) (G.dist w (m₂ i))
      4 * Q + 9 * C + 16 * L + 34 ≤
        4 * rlBudget (slack P) P.length := by
    intro i hi
    dsimp
    exact pureSpan_addTwo_exception_envelope
      (slack P) P.length
      (∑ r : Fin P.length, ∑ q : Fin P.length,
        min (capacity r) (capacity q))
      (∑ r : Fin P.length, capacity r)
      (Nat.dist (G.dist w (m₁ i)) (G.dist w (m₂ i)))
      hs htwo hprofileBounds.2 hprofileBounds.1 (hspanBound i hi)
  have hresult := totalCost_le_rlBudget_of_zeroOrOne_addTwo_levelCuts
    w x₀ m₁ m₂ (G.dist w) (slack P) P.length
    capacity weight exceptional (by omega) (Or.inr htwo)
    hcapacitySq hweightSum.le hcapacitySum hroot hstub
    (fun i => hvertexBound (m₁ i))
    (fun i => hvertexBound (m₂ i))
    haligned hexceptional hcard hRFC hcut hlegal henvelope
  simpa [htwo] using hresult

/-- In the span-two pair, every tip neighbor is on the anchor's BFS level. -/
theorem IsGeodesic.pair_spanTwo_tip_neighbor_level
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (color : G.Coloring Bool) (hP : IsGeodesic P)
    (C : OffCorridorComponent P) (l : ℕ)
    (anchor tip : V)
    (hcomponent : offCorridorComponentFinset C = {anchor, tip})
    (hne : anchor ≠ tip)
    (hAT : G.Adj anchor tip)
    (hinterval : offCorridorComponentIntervalEdges P C =
      Finset.Ico l (l + 2))
    (hlevelA : G.dist w anchor = l + 1)
    (hlevelT : G.dist w tip = l + 2) :
    ∀ y : V, G.Adj tip y → G.dist w y = l + 1 := by
  intro y hty
  by_cases hySupport : y ∈ P.support
  · let j := P.support.idxOf y
    have hjLength : j ≤ P.length := support_idxOf_le_length P hySupport
    have hjGet : P.getVert j = y := P.getVert_support_idxOf hySupport
    have htC : tip ∈ offCorridorComponentFinset C := by simp [hcomponent]
    have hjAttach : j ∈ offCorridorAttachmentIndices P C := by
      exact (mem_offCorridorAttachmentIndices P C j).2
        ⟨hjLength, tip, htC, by simpa [hjGet] using hty⟩
    obtain ⟨_, _, hbounds⟩ :=
      attachment_extrema_of_interval_eq_length P C l 2 (by omega) hinterval
    have hjBounds := hbounds j hjAttach
    have hjLevel : G.dist w y = j := by
      rw [← hjGet]
      exact IsGeodesic.rootDist_getVert hP hjLength
    have hstep := Coloring.adj_rootDist_natDist_eq_one
      (w := w) hconn color hty
    rw [hlevelT, hjLevel] at hstep
    rw [Nat.dist_eq_sub_of_le_right hjBounds.2] at hstep
    omega
  · have htC : tip ∈ offCorridorComponentFinset C := by simp [hcomponent]
    have htComp : tip ∈ C := (mem_offCorridorComponentFinset C).1 htC
    obtain ⟨htOffSet, htCompEq⟩ := ComponentCompl.mem_supp_iff.mp htComp
    have htNot : tip ∉ P.support := by simpa [supportFinset] using htOffSet
    have hcompEq := offCorridorComponentOf_eq_of_adj P htNot hySupport hty
    have htOwn : offCorridorComponentOf P tip htNot = C := by
      simpa [offCorridorComponentOf, supportFinset] using htCompEq
    have hyOwn : y ∈ offCorridorComponentFinset
        (offCorridorComponentOf P y hySupport) :=
      mem_offCorridorComponentOf P hySupport
    have hyC : y ∈ offCorridorComponentFinset C := by
      simpa [← htOwn, hcompEq] using hyOwn
    have hyCases : y = anchor ∨ y = tip := by simpa [hcomponent] using hyC
    rcases hyCases with hyA | hyT
    · subst y
      exact hlevelA
    · subst y
      exact (G.loopless.irrefl _ hty).elim

/-- Every off-corridor vertex other than the span-two tip is an ordinary
two-sided vertex in a length-two component interval. -/
theorem IsGeodesic.massSpan_nonTip_geometry
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P)
    (Cstar : OffCorridorComponent P) (a : ℕ) (anchor tip v : V)
    (hstar : offCorridorComponentFinset Cstar = {anchor, tip})
    (hstarInterval : offCorridorComponentIntervalEdges P Cstar =
      Finset.Ico a (a + 2))
    (hlevelA : G.dist w anchor = a + 1)
    (hleft : G.Adj anchor (P.getVert a))
    (hright : G.Adj anchor (P.getVert (a + 2)))
    (hothers : ∀ C : OffCorridorComponent P, C ≠ Cstar →
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2)
    (hvOff : v ∈ offCorridorFinset P) (hvt : v ≠ tip) :
    ∃ C : OffCorridorComponent P, ∃ l : ℕ,
      v ∈ offCorridorComponentFinset C ∧
      offCorridorComponentIntervalEdges P C = Finset.Ico l (l + 2) ∧
      G.dist w v = l + 1 ∧
      G.Adj v (P.getVert l) ∧
      G.Adj v (P.getVert (l + 2)) := by
  classical
  have hvNot : v ∉ P.support := by
    have := (Finset.mem_sdiff.mp hvOff).2
    simpa [supportFinset] using this
  let C := offCorridorComponentOf P v hvNot
  have hvC : v ∈ offCorridorComponentFinset C :=
    mem_offCorridorComponentOf P hvNot
  by_cases hCstar : C = Cstar
  · have hvStar : v ∈ offCorridorComponentFinset Cstar := by
      simpa [hCstar] using hvC
    have hvCases : v = anchor ∨ v = tip := by simpa [hstar] using hvStar
    rcases hvCases with rfl | htip
    · exact ⟨Cstar, a, by simp [hstar], hstarInterval, hlevelA,
        hleft, hright⟩
    · exact (hvt htip).elim
  · obtain ⟨hsize, hspan⟩ := hothers C hCstar
    obtain ⟨l, hinterval⟩ :=
      offCorridorInterval_eq_Ico_of_card_eq_two P C hspan
    obtain ⟨c, hset, hlevel, hcLeft, hcRight⟩ :=
      IsGeodesic.singleton_spanTwo_geometry
        hconn hP C l hsize hinterval
    have hvc : v = c := by simpa [hset] using hvC
    subst v
    exact ⟨C, l, by simp [hset], hinterval, hlevel, hcLeft, hcRight⟩

/-- Rooted-level profile and named exceptional component in the mixed
mass/span branch. -/
theorem IsGeodesic.massSpan_rootLevelProfile
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    [Fintype (OffCorridorComponent P)]
    (hconn : G.Connected) (color : G.Coloring Bool) (hP : IsGeodesic P)
    (htwo : P.length = 2 * slack P - 2)
    (hnonbridge : ∀ i < P.length,
      ¬G.IsBridge s(P.getVert i, P.getVert (i + 1)))
    (hmixed :
      let components := (Finset.univ : Finset (OffCorridorComponent P))
      let size : OffCorridorComponent P → ℕ := fun C =>
        (offCorridorComponentFinset C).card
      let span : OffCorridorComponent P → ℕ := fun C =>
        (offCorridorComponentIntervalEdges P C).card
      let unionCard :=
        (components.biUnion (offCorridorComponentIntervalEdges P)).card
      MassSpanShape components size span (slack P) unionCard) :
    ∃ Cstar : OffCorridorComponent P, ∃ a : ℕ, ∃ anchor tip : V,
      ∃ levels : Finset ℕ,
      offCorridorComponentFinset Cstar = {anchor, tip} ∧
      anchor ≠ tip ∧ G.Adj anchor tip ∧
      G.Adj anchor (P.getVert a) ∧
      G.Adj anchor (P.getVert (a + 2)) ∧
      G.dist w anchor = a + 1 ∧ G.dist w tip = a + 2 ∧
      offCorridorComponentIntervalEdges P Cstar = Finset.Ico a (a + 2) ∧
      (∀ C : OffCorridorComponent P, C ≠ Cstar →
        (offCorridorComponentFinset C).card = 1 ∧
        (offCorridorComponentIntervalEdges P C).card = 2) ∧
      (Set.univ : Set (OffCorridorComponent P)).PairwiseDisjoint
        (offCorridorComponentIntervalEdges P) ∧
      levels.card = slack P ∧
      (∀ r < P.length, r ∈ levels ∨ r + 1 ∈ levels) ∧
      levels ⊆ Finset.range (P.length + 1) ∧
      (offCorridorFinset P).image (G.dist w) = levels ∧
      Set.InjOn (G.dist w) (offCorridorFinset P : Set V) := by
  classical
  let components : Finset (OffCorridorComponent P) := Finset.univ
  let size : OffCorridorComponent P → ℕ := fun C =>
    (offCorridorComponentFinset C).card
  let interval : OffCorridorComponent P → Finset ℕ :=
    offCorridorComponentIntervalEdges P
  let span : OffCorridorComponent P → ℕ := fun C => (interval C).card
  let unionCard := (components.biUnion interval).card
  change MassSpanShape components size span (slack P) unionCard at hmixed
  rcases hmixed with
    ⟨_hmassOne, _hspanOne, hoverlapZero, Cstar, _hCstar,
      hstarSize, hstarSpan, hothersRaw⟩
  have hothers : ∀ C : OffCorridorComponent P, C ≠ Cstar →
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2 := by
    intro C hC
    have h := hothersRaw C (by simp [components]) hC
    change (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2 at h
    exact h
  have hdisjointFin :
      (components : Set (OffCorridorComponent P)).PairwiseDisjoint interval := by
    apply pairwiseDisjoint_of_overlapDefect_eq_zero components interval
    exact hoverlapZero
  have hdisjoint :
      (Set.univ : Set (OffCorridorComponent P)).PairwiseDisjoint
        (offCorridorComponentIntervalEdges P) := by
    simpa [components, interval] using hdisjointFin
  obtain ⟨a, hstarInterval⟩ :=
    offCorridorInterval_eq_Ico_of_card_eq_two P Cstar (by
      simpa [span, interval] using hstarSpan)
  obtain ⟨anchor, tip, hstar, hne, hAT, hleft, hright,
      hlevelA, hlevelT⟩ :=
    IsGeodesic.pair_spanTwo_geometry
      hconn color hP Cstar a hstarSize hstarInterval
  have hanchorOff : anchor ∈ offCorridorFinset P :=
    mem_offCorridorFinset_of_mem_componentFinset
      (C := Cstar) (by simp [hstar])
  have htipOff : tip ∈ offCorridorFinset P :=
    mem_offCorridorFinset_of_mem_componentFinset
      (C := Cstar) (by simp [hstar])
  have hregular : ∀ v ∈ offCorridorFinset P, v ≠ tip →
      ∃ C : OffCorridorComponent P, ∃ l : ℕ,
        v ∈ offCorridorComponentFinset C ∧
        offCorridorComponentIntervalEdges P C = Finset.Ico l (l + 2) ∧
        G.dist w v = l + 1 ∧
        G.Adj v (P.getVert l) ∧
        G.Adj v (P.getVert (l + 2)) := by
    intro v hv hvt
    exact IsGeodesic.massSpan_nonTip_geometry
      hconn hP Cstar a anchor tip v hstar hstarInterval hlevelA
      hleft hright hothers hv hvt
  have hinjective :
      Set.InjOn (G.dist w) (offCorridorFinset P : Set V) := by
    intro x hx y hy hxy
    by_cases hxt : x = tip
    · subst x
      by_cases hyt : y = tip
      · exact hyt.symm
      · obtain ⟨Cy, ly, hyC, hyInterval, hyLevel, _hyL, _hyR⟩ :=
          hregular y hy hyt
        have hly : ly = a + 1 := by rw [hlevelT, hyLevel] at hxy; omega
        have hCyNe : Cy ≠ Cstar := by
          intro hCy
          subst Cy
          have hyCases : y = anchor ∨ y = tip := by simpa [hstar] using hyC
          rcases hyCases with hyA | hyT
          · subst y
            rw [hlevelA] at hxy
            omega
          · exact hyt hyT
        have hd : Disjoint
            (offCorridorComponentIntervalEdges P Cy)
            (offCorridorComponentIntervalEdges P Cstar) :=
          hdisjoint (x := Cy) (y := Cstar) (by simp) (by simp) hCyNe
        have hmemStar : a + 1 ∈
            offCorridorComponentIntervalEdges P Cstar := by
          rw [hstarInterval]
          simp
        have hmemY : a + 1 ∈ offCorridorComponentIntervalEdges P Cy := by
          rw [hyInterval, hly]
          simp
        exact (Finset.disjoint_left.mp hd hmemY hmemStar).elim
    · by_cases hyt : y = tip
      · subst y
        obtain ⟨Cx, lx, hxC, hxInterval, hxLevel, _hxL, _hxR⟩ :=
          hregular x hx hxt
        have hlx : lx = a + 1 := by rw [hxLevel, hlevelT] at hxy; omega
        have hCxNe : Cx ≠ Cstar := by
          intro hCx
          subst Cx
          have hxCases : x = anchor ∨ x = tip := by simpa [hstar] using hxC
          rcases hxCases with hxA | hxT
          · subst x
            rw [hlevelA] at hxy
            omega
          · exact hxt hxT
        have hd : Disjoint
            (offCorridorComponentIntervalEdges P Cstar)
            (offCorridorComponentIntervalEdges P Cx) :=
          hdisjoint (x := Cstar) (y := Cx) (by simp) (by simp) hCxNe.symm
        have hmemStar : a + 1 ∈
            offCorridorComponentIntervalEdges P Cstar := by
          rw [hstarInterval]
          simp
        have hmemX : a + 1 ∈ offCorridorComponentIntervalEdges P Cx := by
          rw [hxInterval, hlx]
          simp
        exact (Finset.disjoint_left.mp hd hmemStar hmemX).elim
      · obtain ⟨Cx, lx, hxC, hxInterval, hxLevel, _hxL, _hxR⟩ :=
          hregular x hx hxt
        obtain ⟨Cy, ly, hyC, hyInterval, hyLevel, _hyL, _hyR⟩ :=
          hregular y hy hyt
        have hl : lx = ly := by rw [hxLevel, hyLevel] at hxy; omega
        have hcomponents : Cx = Cy := by
          by_contra hneComp
          have hd := hdisjoint (by simp) (by simp) hneComp
          have hmemX : lx ∈ offCorridorComponentIntervalEdges P Cx := by
            rw [hxInterval]
            simp
          have hmemY : lx ∈ offCorridorComponentIntervalEdges P Cy := by
            rw [hyInterval, ← hl]
            simp
          exact (Finset.disjoint_left.mp hd hmemX hmemY).elim
        subst Cy
        by_cases hstarComp : Cx = Cstar
        · subst Cx
          have hxCases : x = anchor ∨ x = tip := by simpa [hstar] using hxC
          have hyCases : y = anchor ∨ y = tip := by simpa [hstar] using hyC
          rcases hxCases with hxA | hxT
          · rcases hyCases with hyA | hyT
            · exact hxA.trans hyA.symm
            · exact (hyt hyT).elim
          · exact (hxt hxT).elim
        · have hsize := (hothers Cx hstarComp).1
          obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hsize
          have hxc : x = c := by simpa [hc] using hxC
          have hyc : y = c := by simpa [hc] using hyC
          exact hxc.trans hyc.symm
  let levels := (offCorridorFinset P).image (G.dist w)
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
  have hlevelsCard : levels.card = slack P := by
    have hcardImage : levels.card = (offCorridorFinset P).card := by
      exact Finset.card_image_iff.mpr hinjective
    rw [hcardImage, hoffCard]
  have hlevelsSub : levels ⊆ Finset.range (P.length + 1) := by
    intro k hk
    obtain ⟨v, hvOff, rfl⟩ := Finset.mem_image.mp hk
    by_cases hvt : v = tip
    · subst v
      have hmem : a + 1 ∈ offCorridorComponentIntervalEdges P Cstar := by
        rw [hstarInterval]
        simp
      have hrange :=
        offCorridorComponentIntervalEdges_subset_range P Cstar hmem
      rw [hlevelT]
      exact Finset.mem_range.mpr (by
        have := Finset.mem_range.mp hrange
        omega)
    · obtain ⟨C, l, _hvC, hinterval, hlevel, _hvL, _hvR⟩ :=
        hregular v hvOff hvt
      have hmem : l + 1 ∈ offCorridorComponentIntervalEdges P C := by
        rw [hinterval]
        simp
      have hrange := offCorridorComponentIntervalEdges_subset_range P C hmem
      rw [hlevel]
      exact Finset.mem_range.mpr (by
        have := Finset.mem_range.mp hrange
        omega)
  have hunion :
      (Finset.univ : Finset (OffCorridorComponent P)).biUnion
        (offCorridorComponentIntervalEdges P) = Finset.range P.length :=
    by
      have hraw :=
        IsGeodesic.biUnion_offCorridorIntervals_eq_range hP hnonbridge
      convert hraw using 1
      apply Finset.Subset.antisymm
      · intro i hi
        obtain ⟨C, _hC, hiC⟩ := Finset.mem_biUnion.mp hi
        exact Finset.mem_biUnion.mpr ⟨C, by simp, hiC⟩
      · intro i hi
        obtain ⟨C, _hC, hiC⟩ := Finset.mem_biUnion.mp hi
        exact Finset.mem_biUnion.mpr ⟨C, by simp, hiC⟩
  have hactive : ∀ r < P.length, r ∈ levels ∨ r + 1 ∈ levels := by
    intro r hr
    have hrUnion : r ∈
        (Finset.univ : Finset (OffCorridorComponent P)).biUnion
          (offCorridorComponentIntervalEdges P) := by
      rw [hunion]
      exact Finset.mem_range.mpr hr
    obtain ⟨C, _hC, hrC⟩ := Finset.mem_biUnion.mp hrUnion
    have hspanC : (offCorridorComponentIntervalEdges P C).card = 2 := by
      by_cases hCstar : C = Cstar
      · subst C
        simpa [hstarInterval]
      · exact (hothers C hCstar).2
    obtain ⟨l, hinterval⟩ :=
      offCorridorInterval_eq_Ico_of_card_eq_two P C hspanC
    have hrBounds := Finset.mem_Ico.mp (by simpa [hinterval] using hrC)
    have hmid : l + 1 ∈ levels := by
      by_cases hCstar : C = Cstar
      · subst C
        have hlMem : l ∈ offCorridorComponentIntervalEdges P Cstar := by
          rw [hinterval]
          simp
        have haMem : a ∈ offCorridorComponentIntervalEdges P Cstar := by
          rw [hstarInterval]
          simp
        rw [hstarInterval] at hlMem
        rw [hinterval] at haMem
        have hl : l = a := by
          have h₁ := Finset.mem_Ico.mp hlMem
          have h₂ := Finset.mem_Ico.mp haMem
          omega
        exact Finset.mem_image.mpr
          ⟨anchor, hanchorOff, by simpa [hl] using hlevelA⟩
      · obtain ⟨hsize, _⟩ := hothers C hCstar
        obtain ⟨c, hset, hlevel, _hcLeft, _hcRight⟩ :=
          IsGeodesic.singleton_spanTwo_geometry
            hconn hP C l hsize hinterval
        have hcOff : c ∈ offCorridorFinset P :=
          mem_offCorridorFinset_of_mem_componentFinset
            (C := C) (by simp [hset])
        exact Finset.mem_image.mpr ⟨c, hcOff, hlevel⟩
    have hrCases : r = l ∨ r = l + 1 := by omega
    rcases hrCases with rfl | rfl
    · exact Or.inr hmid
    · exact Or.inl hmid
  exact ⟨Cstar, a, anchor, tip, levels, hstar, hne, hAT,
    hleft, hright, hlevelA, hlevelT, hstarInterval, hothers,
    hdisjoint, hlevelsCard, hactive, hlevelsSub, rfl, hinjective⟩

/-- All vertices except the mixed mass/span tip have the ordinary corridor
anchors immediately below and above their BFS level. -/
theorem IsGeodesic.massSpan_nonTip_twoSidedAnchors
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ tip : V} {P : G.Walk w x₀}
    (hP : IsGeodesic P)
    (hregular : ∀ v ∈ offCorridorFinset P, v ≠ tip →
      ∃ C : OffCorridorComponent P, ∃ l : ℕ,
        v ∈ offCorridorComponentFinset C ∧
        offCorridorComponentIntervalEdges P C = Finset.Ico l (l + 2) ∧
        G.dist w v = l + 1 ∧
        G.Adj v (P.getVert l) ∧
        G.Adj v (P.getVert (l + 2))) :
    ∀ v : V, v ≠ tip →
      (G.dist w v < P.length →
        G.Adj v (P.getVert (G.dist w v + 1))) ∧
      (0 < G.dist w v →
        G.Adj (P.getVert (G.dist w v - 1)) v) := by
  intro v hvt
  by_cases hvSupport : v ∈ P.support
  · have hvEq : v = P.getVert (G.dist w v) :=
      IsGeodesic.eq_getVert_of_mem_support_rootDist_eq hP hvSupport rfl
    let j := P.support.idxOf v
    have hj : j ≤ P.length := support_idxOf_le_length P hvSupport
    have hget : P.getVert j = v := P.getVert_support_idxOf hvSupport
    have hjLevel : G.dist w (P.getVert j) = j :=
      IsGeodesic.rootDist_getVert hP hj
    rw [hget] at hjLevel
    have hvBound : G.dist w v ≤ P.length := by omega
    constructor
    · intro hvlt
      have hadj := P.adj_getVert_succ hvlt
      rw [← hvEq] at hadj
      exact hadj
    · intro hvpos
      have hpred : G.dist w v - 1 + 1 = G.dist w v := by omega
      have hadj :=
        P.adj_getVert_succ (i := G.dist w v - 1) (by omega)
      rw [hpred, ← hvEq] at hadj
      exact hadj
  · have hvOff : v ∈ offCorridorFinset P :=
      Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ v, by simpa [supportFinset] using hvSupport⟩
    obtain ⟨C, l, hvC, hinterval, hlevel, hleft, hright⟩ :=
      hregular v hvOff hvt
    constructor
    · intro _
      simpa [hlevel] using hright
    · intro _
      simpa [hlevel] using hleft.symm

/-- The standard layer-product cut bound with one forbidden lower-layer
vertex erased. -/
theorem cutSize_levelUpperCut_le_erasedLowerLayerProduct
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (level : V → ℕ)
    (hstep : ∀ {u v : V}, G.Adj u v →
      Nat.dist (level u) (level v) = 1)
    (r : ℕ) (tip : V) (htip : level tip = r)
    (hnoUp : ∀ y : V, G.Adj tip y → level y ≠ r + 1) :
    cutSize G (levelUpperCut level r) ≤
      ((levelLayer level r).erase tip).card *
        (levelLayer level (r + 1)).card := by
  classical
  let T := levelUpperCut level r
  let A := (levelLayer level r).erase tip
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
      have hulow : level u ≤ r := by simpa [T] using huT
      have hdist := hstep huv.symm
      have hur : level u = r := by
        rw [hvr] at hdist
        rw [Nat.dist_eq_sub_of_le (by omega : level u ≤ r + 1)] at hdist
        omega
      have hut : u ≠ tip := by
        intro hut
        subst u
        exact (hnoUp v huv.symm) hvr
      exact Finset.mem_erase.mpr ⟨hut, by simpa [A] using hur⟩
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
    _ = A.card * C.card := by simp [Nat.mul_comm]
    _ = ((levelLayer level r).erase tip).card *
        (levelLayer level (r + 1)).card := by rfl

/-- A legal same-side demand from the mixed mass/span tip is either level
aligned on the left, or is a right-going add-two row whose threshold span
is at most `d-2`. -/
theorem IsGeodesic.massSpan_tip_pair_classification
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ anchor tip y : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (color : G.Coloring Bool) (hP : IsGeodesic P)
    (Cstar : OffCorridorComponent P) (a : ℕ)
    (hstar : offCorridorComponentFinset Cstar = {anchor, tip})
    (hstarInterval : offCorridorComponentIntervalEdges P Cstar =
      Finset.Ico a (a + 2))
    (hAT : G.Adj anchor tip)
    (hleft : G.Adj anchor (P.getVert a))
    (hright : G.Adj anchor (P.getVert (a + 2)))
    (hlevelA : G.dist w anchor = a + 1)
    (hlevelT : G.dist w tip = a + 2)
    (hdisjoint :
      (Set.univ : Set (OffCorridorComponent P)).PairwiseDisjoint
        (offCorridorComponentIntervalEdges P))
    (hregular : ∀ v ∈ offCorridorFinset P, v ≠ tip →
      ∃ C : OffCorridorComponent P, ∃ l : ℕ,
        v ∈ offCorridorComponentFinset C ∧
        offCorridorComponentIntervalEdges P C = Finset.Ico l (l + 2) ∧
        G.dist w v = l + 1 ∧
        G.Adj v (P.getVert l) ∧
        G.Adj v (P.getVert (l + 2)))
    (hinjective : Set.InjOn (G.dist w) (offCorridorFinset P : Set V))
    (hvertexBound : ∀ v : V, G.dist w v ≤ P.length)
    (hanchors : ∀ v : V, v ≠ tip →
      (G.dist w v < P.length →
        G.Adj v (P.getVert (G.dist w v + 1))) ∧
      (0 < G.dist w v →
        G.Adj (P.getVert (G.dist w v - 1)) v))
    (hsame : color tip = color y)
    (hlegal : 4 ≤ G.dist tip y) :
    G.dist tip y = Nat.dist (G.dist w tip) (G.dist w y) ∨
      (G.dist w tip < G.dist w y ∧
        G.dist tip y ≤ Nat.dist (G.dist w tip) (G.dist w y) + 2 ∧
        Nat.dist (G.dist w tip) (G.dist w y) ≤ P.length - 2) := by
  classical
  have htipOff : tip ∈ offCorridorFinset P :=
    mem_offCorridorFinset_of_mem_componentFinset
      (C := Cstar) (by simp [hstar])
  have hqBound : a + 2 ≤ P.length := by
    have := hvertexBound tip
    rw [hlevelT] at this
    exact this
  have hnoOffLeft : ∀ v ∈ offCorridorFinset P, G.dist w v ≠ a := by
    intro v hvOff hvLevel
    by_cases hvt : v = tip
    · subst v
      rw [hlevelT] at hvLevel
      omega
    · obtain ⟨C, l, hvC, hinterval, hlevel, _hvL, _hvR⟩ :=
        hregular v hvOff hvt
      have hl : l + 1 = a := by rw [hlevel] at hvLevel; exact hvLevel
      by_cases hCstar : C = Cstar
      · subst C
        have hvCases : v = anchor ∨ v = tip := by simpa [hstar] using hvC
        rcases hvCases with hvA | hvT
        · subst v
          rw [hlevelA] at hvLevel
          omega
        · exact hvt hvT
      · have hd : Disjoint
            (offCorridorComponentIntervalEdges P Cstar)
            (offCorridorComponentIntervalEdges P C) :=
          hdisjoint (x := Cstar) (y := C) (by simp) (by simp)
            (Ne.symm hCstar)
        have haStar : a ∈ offCorridorComponentIntervalEdges P Cstar := by
          rw [hstarInterval]
          simp
        have haC : a ∈ offCorridorComponentIntervalEdges P C := by
          rw [hinterval]
          exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
        exact (Finset.disjoint_left.mp hd haStar haC).elim
  have htipRight : G.dist tip (P.getVert (a + 2)) ≤ 2 := by
    have hTA : G.dist tip anchor = 1 :=
      dist_eq_one_iff_adj.mpr hAT.symm
    have hAR : G.dist anchor (P.getVert (a + 2)) = 1 :=
      dist_eq_one_iff_adj.mpr hright
    have htri := hconn.dist_triangle
      (u := tip) (v := anchor) (w := P.getVert (a + 2))
    omega
  have hleftTip : G.dist (P.getVert a) tip ≤ 2 := by
    have hLA : G.dist (P.getVert a) anchor = 1 :=
      dist_eq_one_iff_adj.mpr hleft.symm
    have hATd : G.dist anchor tip = 1 := dist_eq_one_iff_adj.mpr hAT
    have htri := hconn.dist_triangle
      (u := P.getVert a) (v := anchor) (w := tip)
    omega
  let b := G.dist w y
  have hbBound : b ≤ P.length := hvertexBound y
  have heven : Even (Nat.dist (a + 2) b) := by
    simpa [b, hlevelT] using
      Coloring.even_natDist_rootLevels_of_eq hconn color w hsame
  have hlower : Nat.dist (a + 2) b ≤ G.dist tip y := by
    simpa [b, hlevelT] using bfsLevel_natDist_le hconn w tip y
  rcases le_total b (a + 2) with hble | hqle
  · by_cases hbeq : b = a + 2
    · have hclose : G.dist tip y ≤ 2 := by
        rcases IsGeodesic.eq_getVert_or_mem_offCorridor hP (v := y) with
          hyPath | hyOff
        · have hyEq : y = P.getVert (a + 2) := by
            simpa [b, hbeq] using hyPath
          subst y
          exact htipRight
        · have hty : tip = y :=
            hinjective htipOff hyOff (by simp [b, hbeq, hlevelT])
          subst y
          simp
      omega
    · have hblt : b < a + 2 := lt_of_le_of_ne hble hbeq
      rw [Nat.dist_eq_sub_of_le_right hble] at heven hlower
      obtain ⟨k, hk⟩ := heven
      have hgapTwo : 2 ≤ a + 2 - b := by omega
      by_cases hgapEq : a + 2 - b = 2
      · have hb : b = a := by omega
        have hyPath : y = P.getVert a := by
          rcases IsGeodesic.eq_getVert_or_mem_offCorridor hP (v := y) with
            hyPath | hyOff
          · simpa [b, hb] using hyPath
          · exact (hnoOffLeft y hyOff (by simpa [b, hb])).elim
        subst y
        have hclose : G.dist tip (P.getVert a) ≤ 2 := by
          simpa [SimpleGraph.dist_comm] using hleftTip
        omega
      · have hgapFour : 4 ≤ a + 2 - b := by omega
        have hyNe : y ≠ tip := by
          intro hyt
          subst y
          dsimp [b] at hblt
          rw [hlevelT] at hblt
          omega
        have hyNext := (hanchors y hyNe).1 (by omega)
        have hleftTip' : G.dist (P.getVert a) tip ≤ a + 2 - a := by
          omega
        have hupper := IsGeodesic.dist_le_levelSub_of_leftEndpointRoute
          (x := y) (z := tip) hconn hP (a := b) (e := a) (b := a + 2)
          (by omega) (by omega) hqBound hyNext hleftTip'
        have heq : G.dist tip y = a + 2 - b := by
          rw [SimpleGraph.dist_comm] at hupper
          omega
        left
        rw [hlevelT]
        simpa [b, Nat.dist_eq_sub_of_le_right hble] using heq
  · by_cases hbeq : b = a + 2
    · have hclose : G.dist tip y ≤ 2 := by
        rcases IsGeodesic.eq_getVert_or_mem_offCorridor hP (v := y) with
          hyPath | hyOff
        · have hyEq : y = P.getVert (a + 2) := by
            simpa [b, hbeq] using hyPath
          subst y
          exact htipRight
        · have hty : tip = y :=
            hinjective htipOff hyOff (by simp [b, hbeq, hlevelT])
          subst y
          simp
      omega
    · have hblt : a + 2 < b := lt_of_le_of_ne hqle (Ne.symm hbeq)
      have hyNe : y ≠ tip := by
        intro hyt
        subst y
        dsimp [b] at hblt
        rw [hlevelT] at hblt
        omega
      have hyPrev := (hanchors y hyNe).2 (by omega)
      have htipRight' : G.dist tip (P.getVert (a + 2)) ≤ a + 2 - a := by
        omega
      have hupper := IsGeodesic.dist_le_levelSub_of_rightEndpointRoute
        (z := tip) (y := y) hconn hP (a := a) (e := a + 2) (b := b)
        (by omega) (by omega) hbBound htipRight' hyPrev
      right
      refine ⟨by simpa [b, hlevelT], ?_, ?_⟩
      · rw [hlevelT, Nat.dist_eq_sub_of_le hqle]
        change G.dist tip y ≤ b - (a + 2) + 2
        omega
      · rw [hlevelT, Nat.dist_eq_sub_of_le hqle]
        have haTwo : 2 ≤ a + 2 := by omega
        omega

theorem totalCost_le_rlBudget_of_massSpan_allNonbridge_sameSide
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    [Fintype (OffCorridorComponent P)]
    (m₁ m₂ : I → V)
    (hconn : G.Connected)
    (color : G.Coloring Bool)
    (hP : IsGeodesic P)
    (htwo : P.length = 2 * slack P - 2)
    (hnonbridge : ∀ i < P.length,
      ¬G.IsBridge s(P.getVert i, P.getVert (i + 1)))
    (hmixed :
      let components :=
        (Finset.univ : Finset (OffCorridorComponent P))
      let size : OffCorridorComponent P → ℕ := fun C =>
        (offCorridorComponentFinset C).card
      let span : OffCorridorComponent P → ℕ := fun C =>
        (offCorridorComponentIntervalEdges P C).card
      let unionCard :=
        (components.biUnion
          (offCorridorComponentIntervalEdges P)).card
      MassSpanShape components size span (slack P) unionCard)
    (hRFC : ∀ T : Finset V, w ∉ T →
      (∑ i : I, separationDemand T (m₁ i) (m₂ i)) +
        (if x₀ ∈ T then 1 else 0) ≤ cutSize G T)
    (hs : 5 ≤ slack P)
    (hlegal : ∀ i, 4 ≤ G.dist (m₁ i) (m₂ i))
    (hsame : ∀ i, color (m₁ i) = color (m₂ i)) :
    (∑ i : I, (G.dist (m₁ i) (m₂ i) + 1) ^ 2) ≤
      rlBudget (slack P) (2 * slack P - 2) := by
  classical
  obtain ⟨Cstar, a, anchor, tip, levels, hstar, hne, hAT,
      hleft, hright, hlevelA, hlevelT, hstarInterval, hothers,
      hdisjoint, hlevelsCard, hactive, hlevelsSub, himage, hinjective⟩ :=
    IsGeodesic.massSpan_rootLevelProfile
      hconn color hP htwo hnonbridge hmixed
  have hregular : ∀ v ∈ offCorridorFinset P, v ≠ tip →
      ∃ C : OffCorridorComponent P, ∃ l : ℕ,
        v ∈ offCorridorComponentFinset C ∧
        offCorridorComponentIntervalEdges P C = Finset.Ico l (l + 2) ∧
        G.dist w v = l + 1 ∧
        G.Adj v (P.getVert l) ∧
        G.Adj v (P.getVert (l + 2)) := by
    intro v hv hvt
    exact IsGeodesic.massSpan_nonTip_geometry
      hconn hP Cstar a anchor tip v hstar hstarInterval hlevelA
      hleft hright hothers hv hvt
  have hanchors : ∀ v : V, v ≠ tip →
      (G.dist w v < P.length →
        G.Adj v (P.getVert (G.dist w v + 1))) ∧
      (0 < G.dist w v →
        G.Adj (P.getVert (G.dist w v - 1)) v) :=
    IsGeodesic.massSpan_nonTip_twoSidedAnchors hP hregular
  have hvertexBound : ∀ v : V, G.dist w v ≤ P.length := by
    intro v
    by_cases hvSupport : v ∈ P.support
    · let j := P.support.idxOf v
      have hj : j ≤ P.length := support_idxOf_le_length P hvSupport
      have hget : P.getVert j = v := P.getVert_support_idxOf hvSupport
      have hlevel := IsGeodesic.rootDist_getVert hP hj
      rw [hget] at hlevel
      omega
    · have hvOff : v ∈ offCorridorFinset P :=
        Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ v, by simpa [supportFinset] using hvSupport⟩
      have hvImage : G.dist w v ∈
          (offCorridorFinset P).image (G.dist w) :=
        Finset.mem_image.mpr ⟨v, hvOff, rfl⟩
      rw [himage] at hvImage
      have hrange := Finset.mem_range.mp (hlevelsSub hvImage)
      omega
  have hstep : ∀ {u v : V}, G.Adj u v →
      Nat.dist (G.dist w u) (G.dist w v) = 1 := by
    intro u v huv
    exact Coloring.adj_rootDist_natDist_eq_one
      (w := w) hconn color huv
  have hlevelsPos : ∀ k ∈ levels, 1 ≤ k := by
    intro k hk
    have hkImage : k ∈ (offCorridorFinset P).image (G.dist w) := by
      simpa [himage] using hk
    obtain ⟨v, hvOff, hvLevel⟩ := Finset.mem_image.mp hkImage
    by_cases hvt : v = tip
    · subst v
      rw [← hvLevel, hlevelT]
      omega
    · obtain ⟨C, l, _hvC, _hinterval, hlevel, _hL, _hR⟩ :=
        hregular v hvOff hvt
      rw [← hvLevel, hlevel]
      omega
  let high : Finset ℕ := (Finset.range P.length).filter fun r =>
    r ∈ levels ∧ r + 1 ∈ levels
  have hhighCard : high.card ≤ 2 := by
    exact activeLevelSet_high_card_le_two levels (slack P) P.length
      htwo hlevelsSub hlevelsPos hlevelsCard hactive
  let extra : ℕ → ℕ := fun k => if k ∈ levels then 1 else 0
  let capacity : Fin P.length → ℕ := fun r =>
    extra r.1 + extra (r.1 + 1) + extra r.1 * extra (r.1 + 1)
  let highFin : Finset (Fin P.length) :=
    (Finset.univ : Finset (Fin P.length)).filter fun r => r.1 ∈ high
  have hhighSub : high ⊆ Finset.range P.length := by
    intro k hk
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
      exact Finset.mem_image.mpr ⟨r, by simp [highFin, r, hk], rfl⟩
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
    by_cases h₀ : r.1 ∈ levels
    · by_cases h₁ : r.1 + 1 ∈ levels
      · have hrHigh : r ∈ highFin := by
          simp [highFin, high, h₀, h₁]
        simp [capacity, extra, h₀, h₁, hrHigh]
      · have hrNot : r ∉ highFin := by
          simp [highFin, high, h₁]
        simp [capacity, extra, h₀, h₁, hrNot]
    · by_cases h₁ : r.1 + 1 ∈ levels
      · have hrNot : r ∉ highFin := by
          simp [highFin, high, h₀]
        simp [capacity, extra, h₀, h₁, hrNot]
      · exfalso
        exact hact.elim h₀ h₁
  let aligned : I → Prop := fun i =>
    G.dist (m₁ i) (m₂ i) =
      Nat.dist (G.dist w (m₁ i)) (G.dist w (m₂ i))
  let T := levelUpperCut (G.dist w) (a + 2)
  have hclass : ∀ i,
      aligned i ∨
        (G.dist (m₁ i) (m₂ i) ≤
            Nat.dist (G.dist w (m₁ i)) (G.dist w (m₂ i)) + 2 ∧
          Nat.dist (G.dist w (m₁ i)) (G.dist w (m₂ i)) ≤
            P.length - 2 ∧
          a + 2 < P.length ∧ Separates T (m₁ i) (m₂ i)) := by
    intro i
    by_cases h₁t : m₁ i = tip
    · have hc := IsGeodesic.massSpan_tip_pair_classification
        (y := m₂ i)
        hconn color hP Cstar a hstar hstarInterval hAT hleft hright
        hlevelA hlevelT hdisjoint hregular hinjective hvertexBound hanchors
        (by simpa [h₁t] using hsame i)
        (by simpa [h₁t] using hlegal i)
      rcases hc with hal | ⟨hlt, hadd, hspan⟩
      · left
        simpa [aligned, h₁t] using hal
      · right
        refine ⟨?_, ?_, ?_, ?_⟩
        · simpa [h₁t] using hadd
        · simpa [h₁t] using hspan
        · have := hvertexBound (m₂ i)
          omega
        · right
          constructor
          · simp [T, h₁t, hlevelT]
          · simpa [T, hlevelT] using hlt
    · by_cases h₂t : m₂ i = tip
      · have hc := IsGeodesic.massSpan_tip_pair_classification
          hconn color hP Cstar a hstar hstarInterval hAT hleft hright
          hlevelA hlevelT hdisjoint hregular hinjective hvertexBound hanchors
          (by simpa [h₂t] using (hsame i).symm)
          (by simpa [h₂t, SimpleGraph.dist_comm] using hlegal i)
        rcases hc with hal | ⟨hlt, hadd, hspan⟩
        · left
          simpa [aligned, h₂t, SimpleGraph.dist_comm, Nat.dist_comm] using hal
        · right
          refine ⟨?_, ?_, ?_, ?_⟩
          · simpa [h₂t, SimpleGraph.dist_comm, Nat.dist_comm] using hadd
          · simpa [h₂t, Nat.dist_comm] using hspan
          · have := hvertexBound (m₁ i)
            omega
          · left
            constructor
            · simpa [T, hlevelT] using hlt
            · simp [T, h₂t, hlevelT]
      · left
        exact IsGeodesic.levelAligned_of_twoSidedAnchors
          hconn hP (hanchors (m₁ i) h₁t).1 (hanchors (m₁ i) h₁t).2
          (hanchors (m₂ i) h₂t).1 (hanchors (m₂ i) h₂t).2
          (hvertexBound _) (hvertexBound _)
          (Coloring.even_natDist_rootLevels_of_eq hconn color w (hsame i))
          (hlegal i)
  let exceptional : I → Prop := fun i => ¬aligned i
  have hexceptionCount :
      ((Finset.univ : Finset I).filter exceptional).card ≤ 1 := by
    by_cases hempty :
        (Finset.univ : Finset I).filter exceptional = ∅
    · simp [hempty]
    · obtain ⟨e, he⟩ :=
        Finset.nonempty_iff_ne_empty.mpr hempty
      have heExc : exceptional e := (Finset.mem_filter.mp he).2
      have heData := hclass e
      rcases heData with heAligned | heData
      · exact (heExc heAligned).elim
      · have hqLt : a + 2 < P.length := heData.2.2.1
        have htipNeighbors := IsGeodesic.pair_spanTwo_tip_neighbor_level
          hconn color hP Cstar a anchor tip hstar hne hAT hstarInterval
          hlevelA hlevelT
        have hnoUp : ∀ y : V, G.Adj tip y →
            G.dist w y ≠ a + 2 + 1 := by
          intro y hty
          rw [htipNeighbors y hty]
          omega
        have hsharpRaw :=
          cutSize_levelUpperCut_le_erasedLowerLayerProduct
            (G.dist w) hstep (a + 2) tip hlevelT hnoUp
        have htipLevel : tip ∈ levelLayer (G.dist w) (a + 2) := by
          simp [hlevelT]
        have hqMem : a + 2 ∈ levels := by
          rw [← himage]
          exact Finset.mem_image.mpr
            ⟨tip, mem_offCorridorFinset_of_mem_componentFinset
              (C := Cstar) (by simp [hstar]), hlevelT⟩
        have hlowerCard :
            (levelLayer (G.dist w) (a + 2)).card = 2 := by
          rw [hlayer (a + 2) (by omega)]
          simp [extra, hqMem]
        have heraseCard :
            ((levelLayer (G.dist w) (a + 2)).erase tip).card = 1 := by
          rw [Finset.card_erase_of_mem htipLevel, hlowerCard]
        have hupperCard :
            (levelLayer (G.dist w) (a + 2 + 1)).card ≤ 2 := by
          rw [hlayer (a + 2 + 1) (by omega)]
          simp [extra]
          split <;> omega
        have hsharp : cutSize G T ≤ 2 := by
          dsimp [T]
          calc
            cutSize G (levelUpperCut (G.dist w) (a + 2)) ≤
                ((levelLayer (G.dist w) (a + 2)).erase tip).card *
                  (levelLayer (G.dist w) (a + 2 + 1)).card := hsharpRaw
            _ ≤ 2 := by rw [heraseCard]; omega
        have hw : w ∉ T := by simp [T]
        have hx : x₀ ∈ T := by
          have hxLevel : G.dist w x₀ = P.length := hP.symm
          simpa [T, hxLevel] using hqLt
        apply rootedCutCondition_atMostOne_cutSupported_exception
          m₁ m₂ w x₀ hRFC T exceptional hw
        · simpa [hx] using hsharp
        · intro i hi
          rcases hclass i with hiAligned | hiData
          · exact (hi hiAligned).elim
          · exact hiData.2.2.2
  have hroot : G.dist w w = 0 := by simp
  have hstub : G.dist w x₀ = P.length := hP.symm
  let exceptionalSet : Finset I :=
    (Finset.univ : Finset I).filter exceptional
  by_cases hempty : exceptionalSet = ∅
  · have haligned : ∀ i, aligned i := by
      intro i
      by_contra hi
      have : i ∈ exceptionalSet := by simp [exceptionalSet, exceptional, hi]
      rw [hempty] at this
      simp at this
    let indicator : Fin P.length → ℕ := fun r =>
      if r ∈ highFin then 1 else 0
    let weight : Fin P.length → ℕ := fun r => 1 + indicator r
    have hindicatorSum : (∑ r : Fin P.length, indicator r) = highFin.card := by
      simp [indicator]
    have hweight : (∑ r : Fin P.length, weight r) ≤ 2 * slack P := by
      have heq : (∑ r : Fin P.length, weight r) =
          P.length + highFin.card := by
        simp only [weight, Finset.sum_add_distrib]
        rw [hindicatorSum]
        simp
      rw [heq]
      omega
    have hcapacityWeight : ∀ r, capacity r ≤ (weight r) ^ 2 := by
      intro r
      by_cases hr : r ∈ highFin
      · have hrCap := hcapacity r
        simp [weight, indicator, hr] at hrCap ⊢
        omega
      · simpa [weight, indicator, hr] using hcapacity r
    have hprofile := twoHighColumns_fin_profile_bounds
      P.length capacity highFin hhighFinCard hcapacity
    have hcapacitySum : (∑ r : Fin P.length, capacity r) ≤
        2 * slack P + 2 := by
      exact hprofile.1.trans (by rw [htwo]; omega)
    have hresult := totalCost_le_rlBudget_of_nearBoundaryCapacityProfile
      w x₀ m₁ m₂ (G.dist w) (slack P) P.length capacity weight
      (by omega) (Or.inr htwo) hcapacityWeight hweight hcapacitySum
      hroot hstub (fun i => hvertexBound _) (fun i => hvertexBound _)
      (fun i => haligned i) hRFC hcut hlegal
    simpa [htwo] using hresult
  · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have heExc : exceptional e := by
      simpa [exceptionalSet] using he
    have hcard : exceptionalSet.card ≤ 1 := by
      simpa [exceptionalSet] using hexceptionCount
    have halignedOther : ∀ i, i ≠ e → aligned i := by
      intro i hie
      by_contra hi
      have hiMem : i ∈ exceptionalSet := by
        simp [exceptionalSet, exceptional, hi]
      have hieq := (Finset.card_le_one.mp hcard) i hiMem e he
      exact hie hieq
    have heClass := hclass e
    rcases heClass with heAligned | heData
    · exact (heExc heAligned).elim
    · have hprofile := twoHighColumns_fin_profile_bounds
        P.length capacity highFin hhighFinCard hcapacity
      have hresult := totalCost_le_rlBudget_of_one_addTwo_levelCuts
        w x₀ m₁ m₂ (G.dist w) (slack P) P.length capacity e
        hroot hstub (fun i => hvertexBound _) (fun i => hvertexBound _)
        (fun i hie => halignedOther i hie) heData.1 hRFC hcut hlegal (by
          dsimp
          exact pureSpan_addTwo_exception_envelope
            (slack P) P.length
            (∑ r : Fin P.length, ∑ q : Fin P.length,
              min (capacity r) (capacity q))
            (∑ r : Fin P.length, capacity r)
            (Nat.dist (G.dist w (m₁ e)) (G.dist w (m₂ e)))
            hs htwo hprofile.2 hprofile.1 heData.2.1)
      simpa [htwo] using hresult


/-- An injective level map away from one named point has fibers given by
the regular-level indicator plus the possible contribution of that point. -/
theorem filter_card_eq_indicator_add_point
    {V : Type*} [DecidableEq V]
    (S : Finset V) (z : V) (level : V → ℕ) (levels : Finset ℕ)
    (hz : z ∈ S)
    (hinjective : Set.InjOn level (S.erase z : Set V))
    (himage : (S.erase z).image level = levels)
    (k : ℕ) :
    (S.filter fun v => level v = k).card =
      (if k ∈ levels then 1 else 0) + (if level z = k then 1 else 0) := by
  classical
  have hregular :
      ((S.erase z).filter fun v => level v = k).card =
        if k ∈ levels then 1 else 0 := by
    by_cases hk : k ∈ levels
    · rw [if_pos hk]
      have hkImage : k ∈ (S.erase z).image level := by simpa [himage]
      obtain ⟨x, hx, hxlevel⟩ := Finset.mem_image.mp hkImage
      have hfiber : (S.erase z).filter (fun v => level v = k) = {x} := by
        ext y
        constructor
        · intro hy
          have hydata := Finset.mem_filter.mp hy
          have hyx : y = x := hinjective hydata.1 hx (by omega)
          simp [hyx]
        · intro hy
          have hyx : y = x := by simpa using hy
          subst y
          exact Finset.mem_filter.mpr ⟨hx, hxlevel⟩
      simp [hfiber]
    · rw [if_neg hk]
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxdata := Finset.mem_filter.mp hx
      have hxImage : level x ∈ (S.erase z).image level :=
        Finset.mem_image.mpr ⟨x, hxdata.1, rfl⟩
      have : k ∈ levels := by simpa [himage, hxdata.2] using hxImage
      exact hk this
  rw [← Finset.insert_erase hz]
  by_cases hzk : level z = k
  · simp [Finset.filter_insert, hzk, hregular, add_comm]
  · simp [Finset.filter_insert, hzk, hregular]

theorem totalCost_le_rlBudget_of_pureSpan_allNonbridge_sameSide
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    [Fintype (OffCorridorComponent P)]
    (m₁ m₂ : I → V)
    (hconn : G.Connected)
    (color : G.Coloring Bool)
    (hP : IsGeodesic P)
    (htwo : P.length = 2 * slack P - 2)
    (hnonbridge : ∀ i < P.length,
      ¬G.IsBridge s(P.getVert i, P.getVert (i + 1)))
    (hpure :
      let components :=
        (Finset.univ : Finset (OffCorridorComponent P))
      let size : OffCorridorComponent P → ℕ := fun C =>
        (offCorridorComponentFinset C).card
      let span : OffCorridorComponent P → ℕ := fun C =>
        (offCorridorComponentIntervalEdges P C).card
      let unionCard :=
        (components.biUnion
          (offCorridorComponentIntervalEdges P)).card
      PureSpanShape components size span (slack P) unionCard)
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
  change PureSpanShape components size span (slack P) unionCard at hpureData
  obtain ⟨_hmassZero, _hspanTwo, hoverlapZero,
      Cleaf, _hCleafMem, hleafSize, hleafSpan, hothersRaw⟩ := hpureData
  have hothers : ∀ C : OffCorridorComponent P, C ≠ Cleaf →
      (offCorridorComponentFinset C).card = 1 ∧
      (offCorridorComponentIntervalEdges P C).card = 2 := by
    intro C hC
    have h := hothersRaw C (by simp [components]) hC
    simpa [size, span, interval] using h
  have hdisjointFin :
      (components : Set (OffCorridorComponent P)).PairwiseDisjoint interval := by
    apply pairwiseDisjoint_of_overlapDefect_eq_zero components interval
    exact hoverlapZero
  have hdisjoint :
      (Set.univ : Set (OffCorridorComponent P)).PairwiseDisjoint
        (offCorridorComponentIntervalEdges P) := by
    simpa [components, interval] using hdisjointFin
  have hunion : components.biUnion interval = Finset.range P.length := by
    have hraw := IsGeodesic.biUnion_offCorridorIntervals_eq_range hP hnonbridge
    convert hraw using 1
    apply Finset.Subset.antisymm
    · intro r hr
      obtain ⟨C, _hC, hrC⟩ := Finset.mem_biUnion.mp hr
      exact Finset.mem_biUnion.mpr ⟨C, by simp, hrC⟩
    · intro r hr
      obtain ⟨C, _hC, hrC⟩ := Finset.mem_biUnion.mp hr
      exact Finset.mem_biUnion.mpr ⟨C, by simp [components], hrC⟩
  obtain ⟨z, a, ha, hleafSet, hzLevel, hneighbors, hleafCut⟩ :=
    IsGeodesic.singleton_spanZero_pendant_geometry
      hconn hP Cleaf hleafSize hleafSpan
  have hzC : z ∈ offCorridorComponentFinset Cleaf := by simp [hleafSet]
  have hzOff : z ∈ offCorridorFinset P :=
    mem_offCorridorFinset_of_mem_componentFinset hzC
  have hzAdj : G.Adj z (P.getVert a) := by
    have : P.getVert a ∈ G.neighborFinset z := by simp [hneighbors]
    simpa using this
  have hzw : z ≠ w := by
    intro h
    subst z
    simp at hzLevel
  have hx₀Support : x₀ ∈ P.support := by
    have h := P.getVert_mem_support P.length
    simpa only [P.getVert_length] using h
  have hzx₀ : z ≠ x₀ := by
    intro h
    subst z
    have hzNotSupport := (Finset.mem_sdiff.mp hzOff).2
    exact hzNotSupport (by simpa [supportFinset] using hx₀Support)
  have hregularBound : ∀ v : V, v ≠ z → G.dist w v ≤ P.length := by
    intro v hvz
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
      obtain ⟨C, l, _hCLeaf, _hCSet, hCInterval, hvLevel⟩ :=
        IsGeodesic.pureSpan_regular_vertex_geometry
          hconn hP Cleaf hleafSet hothers hvOff hvz
      have hmem : l + 1 ∈ offCorridorComponentIntervalEdges P C := by
        rw [hCInterval]
        simp
      have hrange := offCorridorComponentIntervalEdges_subset_range P C hmem
      have hlt := Finset.mem_range.mp hrange
      omega
  let regular : Finset V := offCorridorFinset P \ {z}
  let levels : Finset ℕ := regular.image (G.dist w)
  have hinjective : Set.InjOn (G.dist w) (regular : Set V) := by
    simpa [regular] using
      (IsGeodesic.pureSpan_regular_rootDist_injective
        hconn hP Cleaf hleafSet hothers hdisjoint)
  have hactive : ∀ r < P.length, r ∈ levels ∨ r + 1 ∈ levels := by
    intro r hr
    have hrUnion : r ∈ components.biUnion interval := by
      rw [hunion]
      exact Finset.mem_range.mpr hr
    obtain ⟨C, _hC, hrC⟩ := Finset.mem_biUnion.mp hrUnion
    have hCne : C ≠ Cleaf := by
      intro hEq
      subst C
      have hempty : interval Cleaf = ∅ := Finset.card_eq_zero.mp (by
        simpa [span, interval] using hleafSpan)
      rw [hempty] at hrC
      simp at hrC
    obtain ⟨l, hCInterval⟩ :=
      offCorridorInterval_eq_Ico_of_card_eq_two P C (hothers C hCne).2
    obtain ⟨v, hCSet, hvLevel, _hleft, _hright⟩ :=
      IsGeodesic.singleton_spanTwo_geometry
        hconn hP C l (hothers C hCne).1 hCInterval
    have hvC : v ∈ offCorridorComponentFinset C := by simp [hCSet]
    have hvOff : v ∈ offCorridorFinset P :=
      mem_offCorridorFinset_of_mem_componentFinset hvC
    have hvz : v ≠ z := by
      intro hvz
      subst v
      have hzInC : z ∈ C := (mem_offCorridorComponentFinset C).1 hvC
      have hzInLeaf : z ∈ Cleaf :=
        (mem_offCorridorComponentFinset Cleaf).1 hzC
      obtain ⟨_hzOffC, hzEqC⟩ := ComponentCompl.mem_supp_iff.mp hzInC
      obtain ⟨_hzOffLeaf, hzEqLeaf⟩ :=
        ComponentCompl.mem_supp_iff.mp hzInLeaf
      have : C = Cleaf := by rw [← hzEqC, ← hzEqLeaf]
      exact hCne this
    have hvRegular : v ∈ regular := by
      exact Finset.mem_sdiff.mpr ⟨hvOff, by simpa using hvz⟩
    have hrIco : r ∈ Finset.Ico l (l + 2) := by
      rw [← hCInterval]
      exact hrC
    have hrBounds := Finset.mem_Ico.mp hrIco
    have hrCases : r = l ∨ r = l + 1 := by omega
    rcases hrCases with rfl | rfl
    · right
      exact Finset.mem_image.mpr ⟨v, hvRegular, by omega⟩
    · left
      exact Finset.mem_image.mpr ⟨v, hvRegular, by omega⟩
  have hnoConsecutive : ∀ r < P.length,
      ¬(r ∈ levels ∧ r + 1 ∈ levels) := by
    intro r hr hboth
    obtain ⟨x, hx, hxLevel⟩ := Finset.mem_image.mp hboth.1
    obtain ⟨y, hy, hyLevel⟩ := Finset.mem_image.mp hboth.2
    exact IsGeodesic.pureSpan_regular_no_consecutive_levels
      hconn hP Cleaf hleafSet hothers hdisjoint hx hy (by omega)
  let regularExtra : ℕ → ℕ := fun k => if k ∈ levels then 1 else 0
  let leafExtra : ℕ → ℕ := fun k => if G.dist w z = k then 1 else 0
  let extra : ℕ → ℕ := fun k => regularExtra k + leafExtra k
  have hlayer (k : ℕ) (hk : k ≤ P.length) :
      (levelLayer (G.dist w) k).card = extra k + 1 := by
    have hoffCard := filter_card_eq_indicator_add_point
      (offCorridorFinset P) z (G.dist w) levels hzOff
      (by
        intro x hx y hy hxy
        apply hinjective
        · simpa [regular, and_comm] using hx
        · simpa [regular, and_comm] using hy
        · exact hxy)
      (by
        dsimp [levels]
        apply congrArg (Finset.image (G.dist w))
        ext v
        simp [regular, and_comm]) k
    have hbase := IsGeodesic.levelLayer_card_eq_one_add_offLevelFiber_card hP hk
    rw [hbase]
    change (offLevelFiber P (G.dist w) k).card = _ at hoffCard
    rw [hoffCard]
    simp [extra, regularExtra, leafExtra, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc]
  let high : Finset (Fin P.length) :=
    (Finset.univ : Finset (Fin P.length)).filter fun r =>
      G.dist w z = r.1 ∨ G.dist w z = r.1 + 1
  let weight : Fin P.length → ℕ := fun r =>
    extra r.1 + extra (r.1 + 1)
  let capacity : Fin P.length → ℕ := fun r =>
    extra r.1 + extra (r.1 + 1) + extra r.1 * extra (r.1 + 1)
  have hhighImageSub : high.image Fin.val ⊆
      {G.dist w z, G.dist w z - 1} := by
    intro k hk
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hk
    have hrData := (Finset.mem_filter.mp hr).2
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hhighImageCard : (high.image Fin.val).card = high.card := by
    exact Finset.card_image_iff.mpr (fun _ _ _ _ h => Fin.ext h)
  have hhighCard : high.card ≤ 2 := by
    calc
      high.card = (high.image Fin.val).card := hhighImageCard.symm
      _ ≤ ({G.dist w z, G.dist w z - 1} : Finset ℕ).card :=
        Finset.card_le_card hhighImageSub
      _ ≤ 2 := Finset.card_le_two
  have hprofilePoint (r : Fin P.length) :
      weight r ≤ (if r ∈ high then 2 else 1) ∧
      capacity r ≤ (if r ∈ high then 3 else 1) := by
    have hact := hactive r.1 r.2
    have hnot := hnoConsecutive r.1 r.2
    by_cases h0 : r.1 ∈ levels <;>
      by_cases h1 : r.1 + 1 ∈ levels <;>
      by_cases hz0 : G.dist w z = r.1 <;>
      by_cases hz1 : G.dist w z = r.1 + 1 <;>
      simp [weight, capacity, extra, regularExtra, leafExtra, high,
        h0, h1, hz0, hz1] at hact hnot ⊢ <;> omega
  have hcapacitySq : ∀ r, capacity r ≤ (weight r) ^ 2 := by
    intro r
    exact adjacentExtraCapacity_le_sum_sq (extra r.1) (extra (r.1 + 1))
  have hweightSum : (∑ r : Fin P.length, weight r) ≤ 2 * slack P := by
    calc
      (∑ r : Fin P.length, weight r) ≤
          ∑ r : Fin P.length, (if r ∈ high then 2 else 1) :=
        Finset.sum_le_sum fun r _ => (hprofilePoint r).1
      _ = P.length + high.card := by
        calc
          (∑ r : Fin P.length, (if r ∈ high then 2 else 1)) =
              ∑ r : Fin P.length,
                (1 + if r ∈ high then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro r _
            by_cases hr : r ∈ high <;> simp [hr]
          _ = P.length + high.card := by
            rw [Finset.sum_add_distrib]
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul, mul_one]
            rw [show (∑ r : Fin P.length, if r ∈ high then 1 else 0) =
                high.card by
              simpa using Finset.sum_boole (fun r : Fin P.length => r ∈ high)
                (Finset.univ : Finset (Fin P.length))]
            simp
      _ ≤ P.length + 2 := Nat.add_le_add_left hhighCard P.length
      _ = 2 * slack P := by omega
  have hcapacityProfile : ∀ r,
      capacity r ≤ if r ∈ high then 3 else 1 :=
    fun r => (hprofilePoint r).2
  have htwoHighProfile := twoHighColumns_fin_profile_bounds
    P.length capacity high hhighCard hcapacityProfile
  have hcapacitySum : (∑ r : Fin P.length, capacity r) ≤
      2 * slack P + 2 := by
    have h := htwoHighProfile.1
    omega
  have hstep : ∀ {u v : V}, G.Adj u v →
      Nat.dist (G.dist w u) (G.dist w v) = 1 := by
    intro u v huv
    exact Coloring.adj_rootDist_natDist_eq_one hconn color huv
  let level : V → ℕ := fun v => min (G.dist w v) P.length
  have hcutEq (r : Fin P.length) :
      levelUpperCut level r.1 = levelUpperCut (G.dist w) r.1 := by
    ext v
    simp [levelUpperCut, level, r.2]
  have hcut : ∀ r : Fin P.length,
      cutSize G (levelUpperCut level r.1) ≤ capacity r + 1 := by
    intro r
    rw [hcutEq r]
    have hproduct := cutSize_levelUpperCut_le_layerProduct
      (G.dist w) hstep r.1
    rw [hlayer r.1 (by omega), hlayer (r.1 + 1) (by omega)] at hproduct
    dsimp [capacity]
    nlinarith
  have hroot : level w = 0 := by simp [level]
  have hstub : level x₀ = P.length := by
    simp [level, hP.symm]
  have hendpoint₁ : ∀ i, level (m₁ i) ≤ P.length := by
    intro i
    exact min_le_right _ _
  have hendpoint₂ : ∀ i, level (m₂ i) ≤ P.length := by
    intro i
    exact min_le_right _ _
  let exceptional : I → Prop := fun i =>
    G.dist (m₁ i) (m₂ i) ≠
      Nat.dist (level (m₁ i)) (level (m₂ i))
  have hregularAligned (i : I)
      (h₁z : m₁ i ≠ z) (h₂z : m₂ i ≠ z) :
      G.dist (m₁ i) (m₂ i) =
        Nat.dist (level (m₁ i)) (level (m₂ i)) := by
    have hraw := IsGeodesic.pureSpan_regular_levelAligned
      hconn hP Cleaf hleafSet hothers h₁z h₂z
      (hregularBound (m₁ i) h₁z) (hregularBound (m₂ i) h₂z)
      (Coloring.even_natDist_rootLevels_of_eq hconn color w (hsame i))
      (hlegal i)
    simpa [level, min_eq_left (hregularBound (m₁ i) h₁z),
      min_eq_left (hregularBound (m₂ i) h₂z)] using hraw
  have hincident : ∀ i, exceptional i → m₁ i = z ∨ m₂ i = z := by
    intro i hi
    by_contra hne
    push_neg at hne
    exact hi (hregularAligned i hne.1 hne.2)
  have haligned : ∀ i, ¬ exceptional i →
      G.dist (m₁ i) (m₂ i) =
        Nat.dist (level (m₁ i)) (level (m₂ i)) := by
    intro i hi
    exact not_ne_iff.mp hi
  have hexceptional : ∀ i, exceptional i →
      G.dist (m₁ i) (m₂ i) ≤
        Nat.dist (level (m₁ i)) (level (m₂ i)) + 2 := by
    intro i hi
    rcases hincident i hi with h₁ | h₂
    · have h₂z : m₂ i ≠ z := by
        intro h
        have hbad := hlegal i
        rw [h₁, h] at hbad
        simpa using hbad
      have h := IsGeodesic.pureSpan_leaf_distance_le_clippedLevelDist_add_two
        hconn hP Cleaf hleafSet hothers a P.length ha rfl hzLevel hzAdj
        h₂z (hregularBound (m₂ i) h₂z)
      simpa [h₁, level] using h
    · have h₁z : m₁ i ≠ z := by
        intro h
        have hbad := hlegal i
        rw [h, h₂] at hbad
        simpa using hbad
      have h := IsGeodesic.pureSpan_leaf_distance_le_clippedLevelDist_add_two
        hconn hP Cleaf hleafSet hothers a P.length ha rfl hzLevel hzAdj
        h₁z (hregularBound (m₁ i) h₁z)
      simpa [h₂, level, SimpleGraph.dist_comm, Nat.dist_comm] using h
  have hexceptionCard :
      ((Finset.univ : Finset I).filter exceptional).card ≤ 1 := by
    apply rootedCutCondition_atMostOne_pendant_exception
      m₁ m₂ w x₀ z hRFC exceptional hzw hzx₀ hleafCut.le
    intro i hi
    rcases hincident i hi with h₁ | h₂
    · have h₂z : m₂ i ≠ z := by
        intro h
        have hbad := hlegal i
        rw [h₁, h] at hbad
        simpa using hbad
      left
      simp [h₁, h₂z]
    · have h₁z : m₁ i ≠ z := by
        intro h
        have hbad := hlegal i
        rw [h, h₂] at hbad
        simpa using hbad
      right
      simp [h₂, h₁z]
  have hspanInterior : ∀ i, exceptional i → a < P.length →
      Nat.dist (level (m₁ i)) (level (m₂ i)) ≤ P.length - 2 := by
    intro i hi haLt
    have h₁Bound : G.dist w (m₁ i) ≤ P.length := by
      by_cases h₁z : m₁ i = z
      · rw [h₁z, hzLevel]
        omega
      · exact hregularBound (m₁ i) h₁z
    have h₂Bound : G.dist w (m₂ i) ≤ P.length := by
      by_cases h₂z : m₂ i = z
      · rw [h₂z, hzLevel]
        omega
      · exact hregularBound (m₂ i) h₂z
    have heven : Even (Nat.dist (level (m₁ i)) (level (m₂ i))) := by
      simpa [level, min_eq_left h₁Bound, min_eq_left h₂Bound] using
        (Coloring.even_natDist_rootLevels_of_eq hconn color w (hsame i))
    have hLle : Nat.dist (level (m₁ i)) (level (m₂ i)) ≤ P.length := by
      rw [show level (m₁ i) = G.dist w (m₁ i) by
          simp [level, min_eq_left h₁Bound],
        show level (m₂ i) = G.dist w (m₂ i) by
          simp [level, min_eq_left h₂Bound]]
      rcases le_total (G.dist w (m₁ i)) (G.dist w (m₂ i)) with hle | hle
      · rw [Nat.dist_eq_sub_of_le hle]
        omega
      · rw [Nat.dist_eq_sub_of_le_right hle]
        omega
    have hLne : Nat.dist (level (m₁ i)) (level (m₂ i)) ≠ P.length := by
      intro hL
      have hEq : G.dist (m₁ i) (m₂ i) =
          Nat.dist (level (m₁ i)) (level (m₂ i)) := by
        rw [hL]
        rcases le_total (G.dist w (m₁ i)) (G.dist w (m₂ i)) with hle | hle
        · have hdist : Nat.dist (G.dist w (m₁ i)) (G.dist w (m₂ i)) =
              P.length := by
            simpa [level, min_eq_left h₁Bound, min_eq_left h₂Bound] using hL
          rw [Nat.dist_eq_sub_of_le hle] at hdist
          have h₁zero : G.dist w (m₁ i) = 0 := by omega
          have h₂top : G.dist w (m₂ i) = P.length := by omega
          have h₁w : m₁ i = w :=
            ((hconn.dist_eq_zero_iff (u := w) (v := m₁ i)).mp h₁zero).symm
          rw [h₁w]
          exact h₂top
        · have hdist : Nat.dist (G.dist w (m₁ i)) (G.dist w (m₂ i)) =
              P.length := by
            simpa [level, min_eq_left h₁Bound, min_eq_left h₂Bound] using hL
          rw [Nat.dist_eq_sub_of_le_right hle] at hdist
          have h₂zero : G.dist w (m₂ i) = 0 := by omega
          have h₁top : G.dist w (m₁ i) = P.length := by omega
          have h₂w : m₂ i = w :=
            ((hconn.dist_eq_zero_iff (u := w) (v := m₂ i)).mp h₂zero).symm
          rw [h₂w, SimpleGraph.dist_comm]
          exact h₁top
      exact hi hEq
    obtain ⟨q, hq⟩ := heven
    omega
  have hspanTerminal : ∀ i, exceptional i → a = P.length →
      Nat.dist (level (m₁ i)) (level (m₂ i)) ≤ P.length - 1 := by
    intro i hi haTop
    rcases hincident i hi with h₁ | h₂
    · have h₂z : m₂ i ≠ z := by
        intro h
        have hbad := hlegal i
        rw [h₁, h] at hbad
        simp at hbad
      have h₂Bound := hregularBound (m₂ i) h₂z
      have heven := Coloring.even_natDist_rootLevels_of_eq
        hconn color w (hsame i)
      obtain ⟨q, hq⟩ := heven
      have h₂pos : 1 ≤ G.dist w (m₂ i) := by
        by_contra hpos
        have hzero : G.dist w (m₂ i) = 0 := by omega
        rw [h₁, hzLevel, haTop, hzero] at hq
        simp [Nat.dist] at hq
        omega
      rw [h₁]
      simp only [level]
      rw [min_eq_right (by rw [hzLevel, haTop]; omega),
        min_eq_left h₂Bound,
        Nat.dist_eq_sub_of_le_right h₂Bound]
      omega
    · have h₁z : m₁ i ≠ z := by
        intro h
        have hbad := hlegal i
        rw [h, h₂] at hbad
        simp at hbad
      have h₁Bound := hregularBound (m₁ i) h₁z
      have heven := Coloring.even_natDist_rootLevels_of_eq
        hconn color w (hsame i)
      obtain ⟨q, hq⟩ := heven
      have h₁pos : 1 ≤ G.dist w (m₁ i) := by
        by_contra hpos
        have hzero : G.dist w (m₁ i) = 0 := by omega
        rw [h₂, hzLevel, haTop, hzero] at hq
        simp [Nat.dist] at hq
        omega
      rw [h₂]
      simp only [level]
      rw [min_eq_left h₁Bound,
        min_eq_right (by rw [hzLevel, haTop]; omega),
        Nat.dist_eq_sub_of_le h₁Bound]
      omega
  have hcapacityBaseline (haTop : a = P.length) :
      ∀ r, capacity r ≤ 1 := by
    intro r
    have hrNot : r ∉ high := by
      simp [high, hzLevel, haTop]
      omega
    simpa [hrNot] using hcapacityProfile r
  have henvelope : ∀ i, exceptional i →
      let Q := ∑ r : Fin P.length,
        ∑ q : Fin P.length, min (capacity r) (capacity q)
      let C := ∑ r : Fin P.length, capacity r
      let L := Nat.dist (level (m₁ i)) (level (m₂ i))
      4 * Q + 9 * C + 16 * L + 34 ≤
        4 * rlBudget (slack P) P.length := by
    intro i hi
    dsimp
    by_cases haTop : a = P.length
    · have hbaseProfile := baselineColumns_fin_profile_bounds
        P.length capacity (hcapacityBaseline haTop)
      exact pureSpan_stub_exception_envelope
        (slack P) P.length
        (∑ r : Fin P.length,
          ∑ q : Fin P.length, min (capacity r) (capacity q))
        (∑ r : Fin P.length, capacity r)
        (Nat.dist (level (m₁ i)) (level (m₂ i)))
        hs htwo hbaseProfile.2 hbaseProfile.1
        (hspanTerminal i hi haTop)
    · have haLt : a < P.length := by omega
      exact pureSpan_addTwo_exception_envelope
        (slack P) P.length
        (∑ r : Fin P.length,
          ∑ q : Fin P.length, min (capacity r) (capacity q))
        (∑ r : Fin P.length, capacity r)
        (Nat.dist (level (m₁ i)) (level (m₂ i)))
        hs htwo htwoHighProfile.2 htwoHighProfile.1
        (hspanInterior i hi haLt)
  have hresult := totalCost_le_rlBudget_of_zeroOrOne_addTwo_levelCuts
    w x₀ m₁ m₂ level (slack P) P.length capacity weight exceptional
    (by omega) (Or.inr htwo) hcapacitySq hweightSum hcapacitySum
    hroot hstub hendpoint₁ hendpoint₂ haligned hexceptional
    hexceptionCard hRFC hcut hlegal henvelope
  simpa [htwo] using hresult

/-- The exact `d = 2s - 2` internal-cost closure for every canonical
two-defect off-corridor shape. -/
theorem totalCost_le_rlBudget_of_twoDefect_allNonbridge_sameSide
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    [Fintype (OffCorridorComponent P)]
    (m₁ m₂ : I → V)
    (hconn : G.Connected)
    (color : G.Coloring Bool)
    (hP : IsGeodesic P)
    (htwo : P.length = 2 * slack P - 2)
    (hnonbridge : ∀ i < P.length,
      ¬G.IsBridge s(P.getVert i, P.getVert (i + 1)))
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
  obtain ⟨components, hall, hshape⟩ :=
    IsGeodesic.canonical_twoDefect_five_shapes
      color hP (by omega) htwo hnonbridge
  have hcomponents : components = Finset.univ :=
    Finset.eq_univ_of_forall hall
  subst components
  rcases hshape with
    hpure | hmassSpan | hmassOverlap | hpureSpan | hpureOverlap
  · rcases hpure.2.2.2 with hq3 | hq2q2
    · obtain ⟨C, _hC, hsize, hspan, hothers⟩ := hq3
      exact
        Erdos23GapGBTwoDefectAlignment.totalCost_le_rlBudget_of_q3PureMass_allNonbridge_sameSide
          m₁ m₂ hconn color hP htwo hnonbridge hpure C hsize hspan
          (fun D hDC => hothers D (by simp) hDC)
          hRFC hpairInjective hs hlegal hsame
    · obtain ⟨Ca, _hCa, Cb, _hCb, hne, hsizeA, hspanA,
          hsizeB, hspanB, hothers⟩ := hq2q2
      exact
        Erdos23GapGBTwoDefectAlignment.totalCost_le_rlBudget_of_q2q2PureMass_allNonbridge_sameSide
          m₁ m₂ hconn color hP htwo hnonbridge hpure Ca Cb hne
          hsizeA hspanA hsizeB hspanB
          (fun D hDA hDB => hothers D (by simp) hDA hDB)
          hRFC hs hlegal hsame
  · exact totalCost_le_rlBudget_of_massSpan_allNonbridge_sameSide
      m₁ m₂ hconn color hP htwo hnonbridge hmassSpan
      hRFC hs hlegal hsame
  · exact totalCost_le_rlBudget_of_massOverlap_allNonbridge_sameSide
      m₁ m₂ hconn color hP htwo hnonbridge hmassOverlap
      hRFC hs hlegal hsame
  · exact totalCost_le_rlBudget_of_pureSpan_allNonbridge_sameSide
      m₁ m₂ hconn color hP htwo hnonbridge hpureSpan
      hRFC hs hlegal hsame
  · exact totalCost_le_rlBudget_of_pureOverlap_allNonbridge_sameSide
      m₁ m₂ hconn color hP htwo hnonbridge hpureOverlap
      hRFC hs hlegal hsame

#print axioms totalCost_le_rlBudget_of_massSpan_allNonbridge_sameSide
#print axioms totalCost_le_rlBudget_of_pureSpan_allNonbridge_sameSide
#print axioms totalCost_le_rlBudget_of_twoDefect_allNonbridge_sameSide

#print axioms activeLevelSet_high_card_le_two
#print axioms IsGeodesic.levelAligned_of_twoSidedAnchors
#print axioms IsGeodesic.pair_spanTwo_geometry
#print axioms totalCost_le_rlBudget_of_pureOverlap_allNonbridge_sameSide
#print axioms totalCost_le_rlBudget_of_massOverlap_allNonbridge_sameSide

end Erdos23GapGBTwoDefectFinal
