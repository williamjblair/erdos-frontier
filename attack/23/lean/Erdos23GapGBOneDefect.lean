/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair, OpenAI Codex
-/
import ErdosProblems.Erdos23GapGBEqualityBoundary

/-!
# Erdős 23 G-B: the `d = 2s-1` one-defect boundary

This module formalizes the exact interval-deficit trichotomy one row below
the double-slack equality boundary and sharpens the resource arithmetic for
the residual assumption that there are at least two internal demands.
-/

namespace Erdos23GapGBOneDefect

open scoped BigOperators
open SimpleGraph
open Erdos23GapGA
open Erdos23GapGBSeries
open Erdos23GapGBJoint
open Erdos23GapGBEqualityBoundary

def massDefect {α : Type*} (components : Finset α) (s : ℕ) : ℕ :=
  s - components.card

def spanDefect {α : Type*} (components : Finset α)
    (size span : α → ℕ) : ℕ :=
  ∑ c ∈ components, (size c + 1 - span c)

def overlapDefect {α : Type*} (components : Finset α)
    (span : α → ℕ) (unionCard : ℕ) : ℕ :=
  (∑ c ∈ components, span c) - unionCard

/-- Exact three-term interval deficit identity. -/
theorem intervalDefect_identity
    {α : Type*} [DecidableEq α]
    (components : Finset α) (size span : α → ℕ) (s unionCard : ℕ)
    (hpositive : ∀ c ∈ components, 1 ≤ size c)
    (hmass : ∑ c ∈ components, size c = s)
    (hspan : ∀ c ∈ components, span c ≤ size c + 1)
    (hunion : unionCard ≤ ∑ c ∈ components, span c) :
    massDefect components s + spanDefect components size span +
        overlapDefect components span unionCard =
      2 * s - unionCard := by
  have hcard : components.card ≤ s := by
    calc
      components.card = ∑ _c ∈ components, 1 := by simp
      _ ≤ ∑ c ∈ components, size c := by
        apply Finset.sum_le_sum
        intro c hc
        exact hpositive c hc
      _ = s := hmass
  have hsumSizeAdd : ∑ c ∈ components, (size c + 1) =
      s + components.card := by
    rw [Finset.sum_add_distrib, hmass]
    simp
  have hsumSpan : ∑ c ∈ components, span c ≤ s + components.card := by
    rw [← hsumSizeAdd]
    apply Finset.sum_le_sum
    intro c hc
    exact hspan c hc
  have hspanDef : spanDefect components size span =
      s + components.card - ∑ c ∈ components, span c := by
    unfold spanDefect
    rw [Finset.sum_tsub_distrib components hspan, hsumSizeAdd]
  unfold massDefect overlapDefect
  rw [hspanDef]
  omega

/-- At `unionCard = 2s-1`, exactly one of the mass, span, and overlap
deficits is one. -/
theorem intervalDefect_one_trichotomy
    {α : Type*} [DecidableEq α]
    (components : Finset α) (size span : α → ℕ) (s unionCard : ℕ)
    (hpositive : ∀ c ∈ components, 1 ≤ size c)
    (hmass : ∑ c ∈ components, size c = s)
    (hspan : ∀ c ∈ components, span c ≤ size c + 1)
    (hunion : unionCard ≤ ∑ c ∈ components, span c)
    (hs : 1 ≤ s)
    (hone : unionCard = 2 * s - 1) :
    (massDefect components s = 1 ∧
        spanDefect components size span = 0 ∧
        overlapDefect components span unionCard = 0) ∨
      (massDefect components s = 0 ∧
        spanDefect components size span = 1 ∧
        overlapDefect components span unionCard = 0) ∨
      (massDefect components s = 0 ∧
        spanDefect components size span = 0 ∧
        overlapDefect components span unionCard = 1) := by
  subst unionCard
  have hid := intervalDefect_identity components size span s (2 * s - 1)
    hpositive hmass hspan hunion
  omega

/-- Positive masses summing to the number of indices are all one. -/
theorem all_eq_one_of_positive_sum_eq_card
    {α : Type*} [DecidableEq α] (components : Finset α)
    (size : α → ℕ) (hpositive : ∀ c ∈ components, 1 ≤ size c)
    (hsum : ∑ c ∈ components, size c = components.card) :
    ∀ c ∈ components, size c = 1 := by
  intro c hc
  have hrest : (components.erase c).card ≤
      ∑ x ∈ components.erase c, size x := by
    calc
      (components.erase c).card = ∑ _x ∈ components.erase c, 1 := by simp
      _ ≤ ∑ x ∈ components.erase c, size x := by
        apply Finset.sum_le_sum
        intro x hx
        exact hpositive x (Finset.mem_of_mem_erase hx)
  have hdecomp : (∑ x ∈ components.erase c, size x) + size c =
      components.card := by
    rw [Finset.sum_erase_add _ _ hc, hsum]
  have hcardErase : (components.erase c).card + 1 = components.card :=
    Finset.card_erase_add_one hc
  have hcpos := hpositive c hc
  omega

/-- Zero total span deficit saturates every component span. -/
theorem all_span_saturated_of_spanDefect_eq_zero
    {α : Type*} [DecidableEq α] (components : Finset α)
    (size span : α → ℕ)
    (hspan : ∀ c ∈ components, span c ≤ size c + 1)
    (hzero : spanDefect components size span = 0) :
    ∀ c ∈ components, span c = size c + 1 := by
  intro c hc
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun _ _ => Nat.zero_le _)).1 hzero c hc
  have hcspan := hspan c hc
  unfold spanDefect at hzero
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun _ _ => Nat.zero_le _)).1 hzero c hc
  omega

/-- In the mass-defect case every mass is one or two, and exactly one mass
is two. -/
theorem massDefect_structure
    {α : Type*} [DecidableEq α] (components : Finset α)
    (size : α → ℕ) (s : ℕ)
    (hpositive : ∀ c ∈ components, 1 ≤ size c)
    (hmass : ∑ c ∈ components, size c = s)
    (hdef : massDefect components s = 1) :
    (∀ c ∈ components, size c ≤ 2) ∧
      ∃! c, c ∈ components ∧ size c = 2 := by
  have hcard : components.card = s - 1 := by
    unfold massDefect at hdef
    have hcardLe : components.card ≤ s := by
      calc
        components.card = ∑ _c ∈ components, 1 := by simp
        _ ≤ ∑ c ∈ components, size c := by
          apply Finset.sum_le_sum
          intro c hc
          exact hpositive c hc
        _ = s := hmass
    omega
  have hspos : 1 ≤ s := by
    unfold massDefect at hdef
    omega
  have hs : s = components.card + 1 := by omega
  have hleTwo : ∀ c ∈ components, size c ≤ 2 := by
    intro c hc
    have hrest : (components.erase c).card ≤
        ∑ x ∈ components.erase c, size x := by
      calc
        (components.erase c).card = ∑ _x ∈ components.erase c, 1 := by simp
        _ ≤ ∑ x ∈ components.erase c, size x := by
          apply Finset.sum_le_sum
          intro x hx
          exact hpositive x (Finset.mem_of_mem_erase hx)
    have hdecomp : (∑ x ∈ components.erase c, size x) + size c = s := by
      rw [Finset.sum_erase_add _ _ hc, hmass]
    have hcardErase : (components.erase c).card + 1 = components.card :=
      Finset.card_erase_add_one hc
    omega
  constructor
  · exact hleTwo
  have hexists : ∃ c ∈ components, size c = 2 := by
    by_contra hnone
    push Not at hnone
    have hallOne : ∀ c ∈ components, size c = 1 := by
      intro c hc
      have hpos := hpositive c hc
      have hle := hleTwo c hc
      have hne := hnone c hc
      omega
    have : ∑ c ∈ components, size c = components.card := by
      calc
        ∑ c ∈ components, size c = ∑ _c ∈ components, 1 := by
          apply Finset.sum_congr rfl
          intro c hc
          rw [hallOne c hc]
        _ = components.card := by simp
    omega
  obtain ⟨c, hc, hc2⟩ := hexists
  refine ⟨c, ⟨hc, hc2⟩, ?_⟩
  intro x hx
  rcases hx with ⟨hxmem, hx2⟩
  by_contra hxc
  have hxErase : x ∈ components.erase c := Finset.mem_erase.mpr ⟨hxc, hxmem⟩
  have hdecomp : (∑ y ∈ components.erase c, size y) + size c = s := by
    rw [Finset.sum_erase_add _ _ hc, hmass]
  have hrestCard : (components.erase c).card + 1 = components.card :=
    Finset.card_erase_add_one hc
  -- The total excess above one is exactly one, already used by `c`.
  have hxc' : x = c := by
    have hsumOther : ∑ y ∈ components.erase c, size y =
        (components.erase c).card := by omega
    have hxOne := all_eq_one_of_positive_sum_eq_card
      (components.erase c) size
      (fun y hy => hpositive y (Finset.mem_of_mem_erase hy)) hsumOther x hxErase
    omega
  exact hxc hxc'

/-- A family of natural weights summing to one has a unique index of weight
one. -/
theorem existsUnique_eq_one_of_sum_eq_one
    {α : Type*} [DecidableEq α] (components : Finset α) (f : α → ℕ)
    (hsum : ∑ c ∈ components, f c = 1) :
    ∃! c, c ∈ components ∧ f c = 1 := by
  have hne : ∑ c ∈ components, f c ≠ 0 := by omega
  obtain ⟨c, hc, hcne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hcle : f c ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hc
  have hc1 : f c = 1 := by omega
  refine ⟨c, ⟨hc, hc1⟩, ?_⟩
  intro x hx
  rcases hx with ⟨hx, hx1⟩
  by_contra hxc
  have hxErase : x ∈ components.erase c := Finset.mem_erase.mpr ⟨hxc, hx⟩
  have hxle : f x ≤ ∑ y ∈ components.erase c, f y :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) hxErase
  have hdecomp : (∑ y ∈ components.erase c, f y) + f c = 1 := by
    rw [Finset.sum_erase_add _ _ hc, hsum]
  omega

/-- Zero mass defect makes every positive component mass equal to one. -/
theorem massDefect_zero_forces_unit_sizes
    {α : Type*} [DecidableEq α] (components : Finset α)
    (size : α → ℕ) (s : ℕ)
    (hpositive : ∀ c ∈ components, 1 ≤ size c)
    (hmass : ∑ c ∈ components, size c = s)
    (hzero : massDefect components s = 0) :
    ∀ c ∈ components, size c = 1 := by
  have hcardLe : components.card ≤ s := by
    calc
      components.card = ∑ _c ∈ components, 1 := by simp
      _ ≤ ∑ c ∈ components, size c := by
        apply Finset.sum_le_sum
        intro c hc
        exact hpositive c hc
      _ = s := hmass
  have hcard : components.card = s := by
    unfold massDefect at hzero
    omega
  apply all_eq_one_of_positive_sum_eq_card components size hpositive
  simpa [hcard] using hmass

/-- The span-defect case has singleton components and a unique one-edge
attachment interval; all other intervals have two edges. -/
theorem spanDefect_structure
    {α : Type*} [DecidableEq α] (components : Finset α)
    (size span : α → ℕ) (s : ℕ)
    (hpositive : ∀ c ∈ components, 1 ≤ size c)
    (hmass : ∑ c ∈ components, size c = s)
    (hspan : ∀ c ∈ components, span c ≤ size c + 1)
    (hmassZero : massDefect components s = 0)
    (hspanOne : spanDefect components size span = 1) :
    (∀ c ∈ components, size c = 1) ∧
      ∃! c, c ∈ components ∧ span c = 1 ∧
        ∀ x ∈ components, x ≠ c → span x = 2 := by
  have hunit := massDefect_zero_forces_unit_sizes components size s
    hpositive hmass hmassZero
  constructor
  · exact hunit
  have hsumDef : ∑ c ∈ components, (size c + 1 - span c) = 1 := hspanOne
  obtain ⟨c, ⟨hc, hcDef⟩, hcUnique⟩ :=
    existsUnique_eq_one_of_sum_eq_one components
      (fun x => size x + 1 - span x) hsumDef
  have hcSize := hunit c hc
  have hcSpanLe := hspan c hc
  have hcSpan : span c = 1 := by omega
  have hothers : ∀ x ∈ components, x ≠ c → span x = 2 := by
    intro x hx hxc
    have hxSize := hunit x hx
    have hxSpanLe := hspan x hx
    have hxDefLe : size x + 1 - span x ≤ 1 := by
      calc
        size x + 1 - span x ≤
            ∑ z ∈ components, (size z + 1 - span z) :=
          Finset.single_le_sum
            (f := fun z => size z + 1 - span z)
            (fun _ _ => Nat.zero_le _) hx
        _ = 1 := hsumDef
    have hxDefNe : size x + 1 - span x ≠ 1 := by
      intro hxDef
      exact hxc (hcUnique x ⟨hx, hxDef⟩)
    omega
  refine ⟨c, ⟨hc, hcSpan, hothers⟩, ?_⟩
  intro x hx
  rcases hx with ⟨hxmem, hxspan, _⟩
  have hxSize := hunit x hxmem
  have hxDef : size x + 1 - span x = 1 := by omega
  exact hcUnique x ⟨hxmem, hxDef⟩

/-- Zero overlap deficit is exactly equality in the finite-union cardinality
bound and therefore forces pairwise-disjoint intervals. -/
theorem pairwiseDisjoint_of_overlapDefect_eq_zero
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (components : Finset α) (family : α → Finset β)
    (hzero : overlapDefect components (fun c => (family c).card)
      (components.biUnion family).card = 0) :
    (↑components : Set α).PairwiseDisjoint family := by
  have hunion : (components.biUnion family).card ≤
      ∑ c ∈ components, (family c).card := Finset.card_biUnion_le
  have heq : (components.biUnion family).card =
      ∑ c ∈ components, (family c).card := by
    unfold overlapDefect at hzero
    change (∑ c ∈ components, (family c).card) -
      (components.biUnion family).card = 0 at hzero
    omega
  exact pairwiseDisjoint_of_card_biUnion_eq_sum_card components family heq

/-- In the overlap-defect case every component is singleton, every interval
has two edges, and the total interval multiplicity exceeds the union by
exactly one. -/
theorem overlapDefect_structure
    {α : Type*} [DecidableEq α] (components : Finset α)
    (size span : α → ℕ) (s unionCard : ℕ)
    (hpositive : ∀ c ∈ components, 1 ≤ size c)
    (hmass : ∑ c ∈ components, size c = s)
    (hspan : ∀ c ∈ components, span c ≤ size c + 1)
    (hunion : unionCard ≤ ∑ c ∈ components, span c)
    (hmassZero : massDefect components s = 0)
    (hspanZero : spanDefect components size span = 0)
    (hoverlapOne : overlapDefect components span unionCard = 1) :
    (∀ c ∈ components, size c = 1 ∧ span c = 2) ∧
      (∑ c ∈ components, span c) = unionCard + 1 := by
  have hunit := massDefect_zero_forces_unit_sizes components size s
    hpositive hmass hmassZero
  have hsaturated := all_span_saturated_of_spanDefect_eq_zero
    components size span hspan hspanZero
  constructor
  · intro c hc
    have hcSat := hsaturated c hc
    have hcUnit := hunit c hc
    exact ⟨hcUnit, by rw [hcSat, hcUnit]⟩
  · unfold overlapDefect at hoverlapOne
    change (∑ c ∈ components, span c) - unionCard = 1 at hoverlapOne
    omega

/-- Sharpened resource arithmetic for `d=2s-1`.  The residual hypothesis
`|M|>=2` makes every single resource at most `R-1`, which saves the four
linear units lost when the RL distance drops from `2s` to `2s-1`. -/
theorem totalCost_le_oneDefectBudget_of_resourcePacking
    {I : Type*} [Fintype I] (D resource : I → ℕ) (s : ℕ)
    (hs : 5 ≤ s) (hcard : 2 ≤ Fintype.card I)
    (hpositive : ∀ i, 1 ≤ resource i)
    (hpack : (∑ i : I, resource i) ≤ s - 1)
    (hdistance : ∀ i, D i ≤ 2 * resource i + 2) :
    (∑ i : I, (D i + 1) ^ 2) ≤ rlBudget s (2 * s - 1) := by
  classical
  let R := ∑ i : I, resource i
  have hcardR : Fintype.card I ≤ R := by
    calc
      Fintype.card I = ∑ _i : I, 1 := by simp
      _ ≤ ∑ i : I, resource i := by
        apply Finset.sum_le_sum
        intro i _
        exact hpositive i
  have hRtwo : 2 ≤ R := hcard.trans hcardR
  have hresourceLe : ∀ i, resource i ≤ R - 1 := by
    intro i
    obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card (by omega) i
    have hjErase : j ∈ (Finset.univ : Finset I).erase i :=
      Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩
    have hjle : resource j ≤
        ∑ x ∈ (Finset.univ : Finset I).erase i, resource x :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hjErase
    have hdecomp :
        (∑ x ∈ (Finset.univ : Finset I).erase i, resource x) + resource i = R := by
      simpa [R] using Finset.sum_erase_add (Finset.univ : Finset I)
        resource (Finset.mem_univ i)
    have hjpos := hpositive j
    omega
  have hsquares : (∑ i : I, resource i ^ 2) ≤ (R - 1) * R := by
    calc
      (∑ i : I, resource i ^ 2) ≤
          ∑ i : I, (R - 1) * resource i := by
        apply Finset.sum_le_sum
        intro i _
        have hi := hresourceLe i
        nlinarith
      _ = (R - 1) * R := by simp [R, Finset.mul_sum]
  have hterm : ∀ i, (D i + 1) ^ 2 ≤
      4 * resource i ^ 2 + 12 * resource i + 9 := by
    intro i
    have hi := hdistance i
    nlinarith
  have hsumTerm := Finset.sum_le_sum fun i
      (_hi : i ∈ (Finset.univ : Finset I)) => hterm i
  have haggregate : (∑ i : I, (D i + 1) ^ 2) ≤ 4 * R ^ 2 + 17 * R := by
    calc
      (∑ i : I, (D i + 1) ^ 2) ≤
          ∑ i : I, (4 * resource i ^ 2 + 12 * resource i + 9) := hsumTerm
      _ = 4 * (∑ i : I, resource i ^ 2) + 12 * R +
          9 * Fintype.card I := by
        simp [R, Finset.sum_add_distrib, Finset.mul_sum]
        ring
      _ ≤ 4 * ((R - 1) * R) + 12 * R + 9 * R := by omega
      _ = 4 * R ^ 2 + 17 * R := by
        have : R - 1 + 1 = R := by omega
        nlinarith
  have hR : R ≤ s - 1 := hpack
  have hRsq : R ^ 2 ≤ (s - 1) ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hR hR
  have hnumeric : 4 * R ^ 2 + 17 * R ≤ 5 * s ^ 2 + 2 * s := by
    calc
      4 * R ^ 2 + 17 * R ≤ 4 * (s - 1) ^ 2 + 17 * (s - 1) := by omega
      _ ≤ 5 * s ^ 2 + 2 * s := by
        let t := s - 1
        have hst : s = t + 1 := by simp [t]; omega
        rw [hst]
        have ht : 4 ≤ t := by omega
        simp only [Nat.add_sub_cancel]
        nlinarith
  have hbudget : rlBudget s (2 * s - 1) = 5 * s ^ 2 + 2 * s := by
    have hsne : s ≠ 1 := by omega
    have hodd : (2 * s - 1) % 2 ≠ 0 := by omega
    have hp : partnerDistance (2 * s - 1) = 1 := by
      simp [partnerDistance, hsne, hodd]
    have hsub : (2 * s - 1) + 1 = 2 * s := by omega
    unfold rlBudget
    rw [hp]
    calc
      s * (2 * (2 * s - 1) + 2 + s) + 2 * s * 1 =
          s * (2 * ((2 * s - 1) + 1) + s) + 2 * s := by ring
      _ = s * (2 * (2 * s) + s) + 2 * s := by rw [hsub]
      _ = 5 * s ^ 2 + 2 * s := by ring
  rw [hbudget]
  exact haggregate.trans hnumeric

/-- RFC-facing cut-count landing theorem for `d=2s-1`.  At least two
demands are essential for the sharpened arithmetic. -/
theorem totalCost_le_oneDefectBudget_of_articulationCuts
    {I K : Type*} [Fintype I] [Fintype K]
    (D : I → ℕ) (crosses : I → K → ℕ) (s : ℕ)
    (hs : 5 ≤ s) (hcard : 2 ≤ Fintype.card I)
    (hcuts : Fintype.card K = s - 1)
    (hlegal : ∀ i, 4 ≤ D i)
    (hcapacity : ∀ k, (∑ i : I, crosses i k) ≤ 1)
    (hdistance : ∀ i, D i ≤ 2 * (∑ k : K, crosses i k) + 2) :
    (∑ i : I, (D i + 1) ^ 2) ≤ rlBudget s (2 * s - 1) := by
  let resource : I → ℕ := fun i => ∑ k : K, crosses i k
  have hpositive : ∀ i, 1 ≤ resource i := by
    intro i
    have hD := hlegal i
    have hbound := hdistance i
    simp only [resource] at hbound ⊢
    omega
  have hpack : (∑ i : I, resource i) ≤ s - 1 := by
    calc
      (∑ i : I, resource i) = ∑ k : K, ∑ i : I, crosses i k := by
        simp only [resource]
        rw [Finset.sum_comm]
      _ ≤ ∑ _k : K, 1 := by
        apply Finset.sum_le_sum
        intro k _
        exact hcapacity k
      _ = s - 1 := by simp [hcuts]
  exact totalCost_le_oneDefectBudget_of_resourcePacking
    D resource s hs hcard hpositive hpack (by
      intro i
      exact hdistance i)

/-- Graph/RFC landing theorem for an explicitly constructed family of
`s-1` capacity-two cuts. -/
theorem totalCost_le_oneDefectBudget_of_cutFamily
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (m₁ m₂ : I → V) (w x₀ : V) (s : ℕ)
    (cuts : Fin (s - 1) → Finset V)
    (hs : 5 ≤ s) (hcard : 2 ≤ Fintype.card I)
    (hRFC : ∀ T : Finset V, w ∉ T →
      (∑ i : I, separationDemand T (m₁ i) (m₂ i)) +
        (if x₀ ∈ T then 1 else 0) ≤ cutSize G T)
    (hterminal : ∀ k, separationDemand (cuts k) w x₀ = 1)
    (hcutSize : ∀ k, cutSize G (cuts k) ≤ 2)
    (hlegal : ∀ i, 4 ≤ G.dist (m₁ i) (m₂ i))
    (hdistance : ∀ i, G.dist (m₁ i) (m₂ i) ≤
      2 * (∑ k, separationDemand (cuts k) (m₁ i) (m₂ i)) + 2) :
    (∑ i : I, (G.dist (m₁ i) (m₂ i) + 1) ^ 2) ≤
      rlBudget s (2 * s - 1) := by
  classical
  have hsym := symmetricRootedCutCondition_of_rootForm G m₁ m₂ w x₀ hRFC
  apply totalCost_le_oneDefectBudget_of_articulationCuts
    (I := I) (K := Fin (s - 1))
    (fun i => G.dist (m₁ i) (m₂ i))
    (fun i k => separationDemand (cuts k) (m₁ i) (m₂ i))
    s hs hcard
  · simp
  · exact hlegal
  · intro k
    have hcut := hsym (cuts k)
    have ht := hterminal k
    have hc := hcutSize k
    omega
  · exact hdistance

/-- The exact one-defect trichotomy instantiated on the canonical components
of an all-nonbridge geodesic of length `2s-1`. -/
theorem IsGeodesic.canonical_oneDefect_trichotomy
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ : V} {P : G.Walk w x₀}
    (hP : IsGeodesic P) (hs : 1 ≤ slack P)
    (hone : P.length = 2 * slack P - 1)
    (hnonbridge : ∀ i < P.length,
      ¬G.IsBridge s(P.getVert i, P.getVert (i + 1))) :
    ∃ components : Finset (OffCorridorComponent P),
      (∀ C, C ∈ components) ∧
      let size : OffCorridorComponent P → ℕ := fun C =>
        (offCorridorComponentFinset C).card
      let span : OffCorridorComponent P → ℕ := fun C =>
        (offCorridorComponentIntervalEdges P C).card
      let unionCard :=
        (components.biUnion (offCorridorComponentIntervalEdges P)).card
      (massDefect components (slack P) = 1 ∧
          spanDefect components size span = 0 ∧
          overlapDefect components span unionCard = 0) ∨
        (massDefect components (slack P) = 0 ∧
          spanDefect components size span = 1 ∧
          overlapDefect components span unionCard = 0) ∨
        (massDefect components (slack P) = 0 ∧
          spanDefect components size span = 0 ∧
          overlapDefect components span unionCard = 1) := by
  classical
  letI : Fintype (OffCorridorComponent P) := Fintype.ofFinite _
  let components : Finset (OffCorridorComponent P) := Finset.univ
  let size : OffCorridorComponent P → ℕ := fun C =>
    (offCorridorComponentFinset C).card
  let interval : OffCorridorComponent P → Finset ℕ :=
    offCorridorComponentIntervalEdges P
  let span : OffCorridorComponent P → ℕ := fun C => (interval C).card
  let unionCard := (components.biUnion interval).card
  have hpositive : ∀ C ∈ components, 1 ≤ size C := by
    intro C _
    exact offCorridorComponentFinset_card_pos C
  have hmassRaw : ∑ C : OffCorridorComponent P,
      (offCorridorComponentFinset C).card =
      ((Finset.univ : Finset V) \ supportFinset P).card := by
    simpa using sum_card_inter_offCorridorComponent P (Finset.univ : Finset V)
  have hmass : ∑ C ∈ components, size C = slack P := by
    simp only [components, size]
    rw [hmassRaw, Finset.card_sdiff]
    simp only [Finset.inter_univ, Finset.card_univ, slack]
    have hsupp := hP.card_supportFinset
    have hle : P.length + 1 ≤ Fintype.card V := by
      rw [← hsupp]
      exact Finset.card_le_univ _
    omega
  have hspan : ∀ C ∈ components, span C ≤ size C + 1 := by
    intro C _
    rw [show span C = offCorridorComponentSpan P C by
      simpa [span, interval] using card_offCorridorComponentIntervalEdges P C]
    exact hP.offCorridorComponentSpan_le_card_add_one C
  have hcover : Finset.range P.length ⊆ components.biUnion interval := by
    intro i hi
    have hiLength : i < P.length := Finset.mem_range.mp hi
    obtain ⟨C, hC⟩ :=
      hP.exists_offCorridorComponent_coversIndex_of_not_isBridge hiLength
        (hnonbridge i hiLength)
    exact Finset.mem_biUnion.mpr
      ⟨C, Finset.mem_univ C,
        mem_offCorridorComponentIntervalEdges_of_coversIndex P C hC⟩
  have hsubset : components.biUnion interval ⊆ Finset.range P.length := by
    intro i hi
    obtain ⟨C, _hC, hiC⟩ := Finset.mem_biUnion.mp hi
    exact offCorridorComponentIntervalEdges_subset_range P C hiC
  have hunionEq : components.biUnion interval = Finset.range P.length :=
    Finset.Subset.antisymm hsubset hcover
  have hunionValue : unionCard = 2 * slack P - 1 := by
    simp [unionCard, hunionEq, hone]
  have hunionBound : unionCard ≤ ∑ C ∈ components, span C := by
    exact Finset.card_biUnion_le
  refine ⟨components, by simp [components], ?_⟩
  simpa [size, span, interval, unionCard] using
    intervalDefect_one_trichotomy components size span (slack P) unionCard
      hpositive hmass hspan hunionBound hs hunionValue

/-- A singleton off-corridor component cannot have attachment span one in a
proper Boolean coloring: it would be adjacent to both endpoints of a corridor
edge and create an odd triangle. -/
theorem no_singleton_offCorridorComponent_span_one
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ : V} (color : G.Coloring Bool)
    (P : G.Walk w x₀) (C : OffCorridorComponent P)
    (hsize : (offCorridorComponentFinset C).card = 1)
    (hspan : (offCorridorComponentIntervalEdges P C).card = 1) : False := by
  classical
  obtain ⟨c, hcset⟩ := Finset.card_eq_one.mp hsize
  let A := offCorridorAttachmentIndices P C
  have hintervalNonempty : (offCorridorComponentIntervalEdges P C).Nonempty := by
    apply Finset.card_pos.mp
    omega
  have hA : A.Nonempty := by
    by_contra hempty
    have hinterEmpty : offCorridorComponentIntervalEdges P C = ∅ := by
      simp [offCorridorComponentIntervalEdges, A, hempty]
    rw [hinterEmpty] at hintervalNonempty
    exact Finset.not_nonempty_empty hintervalNonempty
  have hinterval : offCorridorComponentIntervalEdges P C =
      Finset.Ico (A.min' hA) (A.max' hA) := by
    simp [offCorridorComponentIntervalEdges, A, hA]
  have hcardIco : (Finset.Ico (A.min' hA) (A.max' hA)).card = 1 := by
    rw [← hinterval]
    exact hspan
  have hdiff : A.max' hA - A.min' hA = 1 := by
    simpa [Nat.card_Ico] using hcardIco
  have hminmax : A.max' hA = A.min' hA + 1 := by
    have hminle := A.min'_le_max' hA
    omega
  have hminMem : A.min' hA ∈ offCorridorAttachmentIndices P C := by
    simpa [A] using A.min'_mem hA
  have hmaxMem : A.max' hA ∈ offCorridorAttachmentIndices P C := by
    simpa [A] using A.max'_mem hA
  obtain ⟨hminLength, cL, hcL, hAdjL⟩ :=
    (mem_offCorridorAttachmentIndices P C (A.min' hA)).1 hminMem
  obtain ⟨hmaxLength, cR, hcR, hAdjR⟩ :=
    (mem_offCorridorAttachmentIndices P C (A.max' hA)).1 hmaxMem
  have hcL' : cL = c := by simpa [hcset] using hcL
  have hcR' : cR = c := by simpa [hcset] using hcR
  subst cL
  subst cR
  have hindex : A.min' hA < P.length := by omega
  have hPathAdj : G.Adj (P.getVert (A.min' hA))
      (P.getVert (A.min' hA + 1)) := P.adj_getVert_succ hindex
  have hColorL := color.valid hAdjL
  have hColorR := color.valid hAdjR
  have hColorPath := color.valid hPathAdj
  rw [hminmax] at hColorR
  cases hc : color c <;>
    cases hl : color (P.getVert (A.min' hA)) <;>
    cases hr : color (P.getVert (A.min' hA + 1)) <;>
    simp_all

/-- The abstract span-defect alternative is impossible for the canonical
component family of a properly two-colored graph. -/
theorem canonical_spanDefect_case_false
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ : V} (color : G.Coloring Bool)
    (P : G.Walk w x₀) (components : Finset (OffCorridorComponent P))
    (hpositive : ∀ C ∈ components,
      1 ≤ (offCorridorComponentFinset C).card)
    (hmass : ∑ C ∈ components, (offCorridorComponentFinset C).card = slack P)
    (hspan : ∀ C ∈ components,
      (offCorridorComponentIntervalEdges P C).card ≤
        (offCorridorComponentFinset C).card + 1)
    (hmassZero : massDefect components (slack P) = 0)
    (hspanOne : spanDefect components
      (fun C => (offCorridorComponentFinset C).card)
      (fun C => (offCorridorComponentIntervalEdges P C).card) = 1) : False := by
  classical
  obtain ⟨_hunit, C, hC, _hunique⟩ := spanDefect_structure components
    (fun X => (offCorridorComponentFinset X).card)
    (fun X => (offCorridorComponentIntervalEdges P X).card)
    (slack P) hpositive hmass hspan hmassZero hspanOne
  exact no_singleton_offCorridorComponent_span_one color P C
    (_hunit C hC.1) hC.2.1

#print axioms intervalDefect_identity
#print axioms intervalDefect_one_trichotomy
#print axioms massDefect_structure
#print axioms spanDefect_structure
#print axioms overlapDefect_structure
#print axioms totalCost_le_oneDefectBudget_of_resourcePacking
#print axioms totalCost_le_oneDefectBudget_of_articulationCuts
#print axioms totalCost_le_oneDefectBudget_of_cutFamily
#print axioms IsGeodesic.canonical_oneDefect_trichotomy
#print axioms no_singleton_offCorridorComponent_span_one
#print axioms canonical_spanDefect_case_false

end Erdos23GapGBOneDefect
