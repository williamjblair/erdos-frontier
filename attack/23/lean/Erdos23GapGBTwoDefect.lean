/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair, OpenAI Codex
-/
import ErdosProblems.Erdos23GapGBOneDefect
import ErdosProblems.Erdos23GapGBLayerCapacity

/-!
# Erdős 23 G-B: the `d = 2s-2` two-defect boundary

This module classifies the exact canonical interval ledger two rows below
the double-slack equality boundary.  It does not assert the final graph cut
construction or RL bound for this row.
-/

namespace Erdos23GapGBTwoDefect

open scoped BigOperators
open SimpleGraph
open Erdos23GapGA
open Erdos23GapGBSeries
open Erdos23GapGBJoint
open Erdos23GapGBEqualityBoundary
open Erdos23GapGBOneDefect
open Erdos23GapGBBinaryLayers
open Erdos23GapGBLayerCapacity

/-- A finite family of natural weights with total two is supported either
at one index with weight two or at two distinct indices with weight one. -/
theorem sum_eq_two_cases
    {α : Type*} [DecidableEq α] (indices : Finset α) (f : α → ℕ)
    (hsum : ∑ i ∈ indices, f i = 2) :
    (∃ a ∈ indices, f a = 2 ∧
        ∀ x ∈ indices, x ≠ a → f x = 0) ∨
      (∃ a ∈ indices, ∃ b ∈ indices, a ≠ b ∧
        f a = 1 ∧ f b = 1 ∧
        ∀ x ∈ indices, x ≠ a → x ≠ b → f x = 0) := by
  have hne : ∑ i ∈ indices, f i ≠ 0 := by omega
  obtain ⟨a, ha, hane⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hale : f a ≤ 2 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) ha
  have haCases : f a = 1 ∨ f a = 2 := by omega
  rcases haCases with haone | hatwo
  · right
    have hrest : ∑ x ∈ indices.erase a, f x = 1 := by
      have hdecomp : (∑ x ∈ indices.erase a, f x) + f a = 2 := by
        rw [Finset.sum_erase_add _ _ ha, hsum]
      omega
    obtain ⟨b, ⟨hbErase, hbone⟩, _hbUnique⟩ :=
      existsUnique_eq_one_of_sum_eq_one (indices.erase a) f hrest
    have hb : b ∈ indices := Finset.mem_of_mem_erase hbErase
    have hab : a ≠ b := by
      exact fun hab => (Finset.mem_erase.mp hbErase).1 hab.symm
    refine ⟨a, ha, b, hb, hab, haone, hbone, ?_⟩
    intro x hx hxa hxb
    have hxRest : x ∈ (indices.erase a).erase b := by
      exact Finset.mem_erase.mpr
        ⟨hxb, Finset.mem_erase.mpr ⟨hxa, hx⟩⟩
    have hrestZero : ∑ y ∈ (indices.erase a).erase b, f y = 0 := by
      have hdecomp :
          (∑ y ∈ (indices.erase a).erase b, f y) + f b = 1 := by
        rw [Finset.sum_erase_add _ _ hbErase, hrest]
      omega
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun _ _ => Nat.zero_le _)).1 hrestZero x hxRest
  · left
    refine ⟨a, ha, hatwo, ?_⟩
    intro x hx hxa
    have hxErase : x ∈ indices.erase a := Finset.mem_erase.mpr ⟨hxa, hx⟩
    have hrestZero : ∑ y ∈ indices.erase a, f y = 0 := by
      have hdecomp : (∑ y ∈ indices.erase a, f y) + f a = 2 := by
        rw [Finset.sum_erase_add _ _ ha, hsum]
      omega
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun _ _ => Nat.zero_le _)).1 hrestZero x hxErase

/-- At union size `2s-2`, the mass, span, and overlap deficits have total
two, giving the six exact aggregate allocations. -/
theorem intervalDefect_two_six_cases
    {α : Type*} [DecidableEq α]
    (components : Finset α) (size span : α → ℕ) (s unionCard : ℕ)
    (hpositive : ∀ c ∈ components, 1 ≤ size c)
    (hmass : ∑ c ∈ components, size c = s)
    (hspan : ∀ c ∈ components, span c ≤ size c + 1)
    (hunion : unionCard ≤ ∑ c ∈ components, span c)
    (hs : 1 ≤ s) (htwo : unionCard = 2 * s - 2) :
    (massDefect components s = 2 ∧
        spanDefect components size span = 0 ∧
        overlapDefect components span unionCard = 0) ∨
      (massDefect components s = 1 ∧
        spanDefect components size span = 1 ∧
        overlapDefect components span unionCard = 0) ∨
      (massDefect components s = 1 ∧
        spanDefect components size span = 0 ∧
        overlapDefect components span unionCard = 1) ∨
      (massDefect components s = 0 ∧
        spanDefect components size span = 2 ∧
        overlapDefect components span unionCard = 0) ∨
      (massDefect components s = 0 ∧
        spanDefect components size span = 1 ∧
        overlapDefect components span unionCard = 1) ∨
      (massDefect components s = 0 ∧
        spanDefect components size span = 0 ∧
        overlapDefect components span unionCard = 2) := by
  subst unionCard
  have hid := intervalDefect_identity components size span s (2 * s - 2)
    hpositive hmass hspan hunion
  omega

/-- The mass defect is the total component-size excess above one. -/
theorem massDefect_eq_sum_pred
    {α : Type*} [DecidableEq α] (components : Finset α)
    (size : α → ℕ) (s : ℕ)
    (hpositive : ∀ c ∈ components, 1 ≤ size c)
    (hmass : ∑ c ∈ components, size c = s) :
    massDefect components s = ∑ c ∈ components, (size c - 1) := by
  unfold massDefect
  rw [← hmass]
  rw [Finset.sum_tsub_distrib components hpositive]
  simp

/-- Mass defect two has exactly the two integer-partition shapes: one
component of size three, or two components of size two.  All unlisted
components are singletons. -/
theorem massDefect_two_structure
    {α : Type*} [DecidableEq α] (components : Finset α)
    (size : α → ℕ) (s : ℕ)
    (hpositive : ∀ c ∈ components, 1 ≤ size c)
    (hmass : ∑ c ∈ components, size c = s)
    (hdef : massDefect components s = 2) :
    (∃ a ∈ components, size a = 3 ∧
        ∀ x ∈ components, x ≠ a → size x = 1) ∨
      (∃ a ∈ components, ∃ b ∈ components, a ≠ b ∧
        size a = 2 ∧ size b = 2 ∧
        ∀ x ∈ components, x ≠ a → x ≠ b → size x = 1) := by
  have hsumPred : ∑ c ∈ components, (size c - 1) = 2 := by
    rw [← massDefect_eq_sum_pred components size s hpositive hmass]
    exact hdef
  rcases sum_eq_two_cases components (fun c => size c - 1) hsumPred with
      hthree | htwo
  · left
    obtain ⟨a, ha, haexcess, hothers⟩ := hthree
    refine ⟨a, ha, by have := hpositive a ha; omega, ?_⟩
    intro x hx hxa
    have hxpos := hpositive x hx
    have hxzero := hothers x hx hxa
    omega
  · right
    obtain ⟨a, ha, b, hb, hab, haexcess, hbexcess, hothers⟩ := htwo
    refine ⟨a, ha, b, hb, hab,
      by have := hpositive a ha; omega,
      by have := hpositive b hb; omega, ?_⟩
    intro x hx hxa hxb
    have hxpos := hpositive x hx
    have hxzero := hothers x hx hxa hxb
    omega

/-- With zero mass defect, span defect two has exactly two possible support
patterns before bipartiteness is used: one span-zero singleton or two
span-one singletons. -/
theorem spanDefect_two_unit_structure
    {α : Type*} [DecidableEq α] (components : Finset α)
    (size span : α → ℕ) (s : ℕ)
    (hpositive : ∀ c ∈ components, 1 ≤ size c)
    (hmass : ∑ c ∈ components, size c = s)
    (hspan : ∀ c ∈ components, span c ≤ size c + 1)
    (hmassZero : massDefect components s = 0)
    (hspanTwo : spanDefect components size span = 2) :
    (∃ a ∈ components, size a = 1 ∧ span a = 0 ∧
        ∀ x ∈ components, x ≠ a → size x = 1 ∧ span x = 2) ∨
      (∃ a ∈ components, ∃ b ∈ components, a ≠ b ∧
        size a = 1 ∧ span a = 1 ∧
        size b = 1 ∧ span b = 1 ∧
        ∀ x ∈ components, x ≠ a → x ≠ b →
          size x = 1 ∧ span x = 2) := by
  have hunit := massDefect_zero_forces_unit_sizes components size s
    hpositive hmass hmassZero
  have hsum : ∑ c ∈ components, (size c + 1 - span c) = 2 := hspanTwo
  rcases sum_eq_two_cases components
      (fun c => size c + 1 - span c) hsum with hone | htwo
  · left
    obtain ⟨a, ha, hadef, hothers⟩ := hone
    have hasize := hunit a ha
    have haspanLe := hspan a ha
    refine ⟨a, ha, hasize, by omega, ?_⟩
    intro x hx hxa
    have hxsize := hunit x hx
    have hxspanLe := hspan x hx
    have hxzero := hothers x hx hxa
    exact ⟨hxsize, by omega⟩
  · right
    obtain ⟨a, ha, b, hb, hab, hadef, hbdef, hothers⟩ := htwo
    have hasize := hunit a ha
    have hbsize := hunit b hb
    have haspanLe := hspan a ha
    have hbspanLe := hspan b hb
    refine ⟨a, ha, b, hb, hab, hasize, by omega, hbsize, by omega, ?_⟩
    intro x hx hxa hxb
    have hxsize := hunit x hx
    have hxspanLe := hspan x hx
    have hxzero := hothers x hx hxa hxb
    exact ⟨hxsize, by omega⟩

/-- If singleton span-one components are forbidden, pure span defect two
has one and only one span-zero singleton; all other components are saturated
singletons of span two. -/
theorem pureSpanTwo_structure_of_no_unit_span_one
    {α : Type*} [DecidableEq α] (components : Finset α)
    (size span : α → ℕ) (s : ℕ)
    (hpositive : ∀ c ∈ components, 1 ≤ size c)
    (hmass : ∑ c ∈ components, size c = s)
    (hspan : ∀ c ∈ components, span c ≤ size c + 1)
    (hforbid : ∀ c ∈ components, size c = 1 → span c = 1 → False)
    (hmassZero : massDefect components s = 0)
    (hspanTwo : spanDefect components size span = 2) :
    ∃ a ∈ components, size a = 1 ∧ span a = 0 ∧
      ∀ x ∈ components, x ≠ a → size x = 1 ∧ span x = 2 := by
  rcases spanDefect_two_unit_structure components size span s
    hpositive hmass hspan hmassZero hspanTwo with hone | htwo
  · exact hone
  · obtain ⟨a, ha, _b, _hb, _hab, hasize, haspan, _⟩ := htwo
    exact (hforbid a ha hasize haspan).elim

/-- The aggregate allocation `(mass,span,overlap)=(0,1,1)` is impossible
whenever singleton span-one components are forbidden. -/
theorem massZero_spanOne_false_of_no_unit_span_one
    {α : Type*} [DecidableEq α] (components : Finset α)
    (size span : α → ℕ) (s : ℕ)
    (hpositive : ∀ c ∈ components, 1 ≤ size c)
    (hmass : ∑ c ∈ components, size c = s)
    (hspan : ∀ c ∈ components, span c ≤ size c + 1)
    (hforbid : ∀ c ∈ components, size c = 1 → span c = 1 → False)
    (hmassZero : massDefect components s = 0)
    (hspanOne : spanDefect components size span = 1) : False := by
  have hunit := massDefect_zero_forces_unit_sizes components size s
    hpositive hmass hmassZero
  obtain ⟨c, ⟨hc, hcdef⟩, _hunique⟩ :=
    existsUnique_eq_one_of_sum_eq_one components
      (fun x => size x + 1 - span x) hspanOne
  have hcsize := hunit c hc
  have hcspanLe := hspan c hc
  have hcspan : span c = 1 := by omega
  exact hforbid c hc hcsize hcspan

/-- In the mixed `(mass,span)=(1,1)` allocation, bipartiteness forces the
unique span loss onto the unique size-two component.  Its interval has span
two, and every other component is a saturated singleton. -/
theorem massOne_spanOne_structure_of_no_unit_span_one
    {α : Type*} [DecidableEq α] (components : Finset α)
    (size span : α → ℕ) (s : ℕ)
    (hpositive : ∀ c ∈ components, 1 ≤ size c)
    (hmass : ∑ c ∈ components, size c = s)
    (hspan : ∀ c ∈ components, span c ≤ size c + 1)
    (hforbid : ∀ c ∈ components, size c = 1 → span c = 1 → False)
    (hmassOne : massDefect components s = 1)
    (hspanOne : spanDefect components size span = 1) :
    ∃ a ∈ components, size a = 2 ∧ span a = 2 ∧
      ∀ x ∈ components, x ≠ a → size x = 1 ∧ span x = 2 := by
  obtain ⟨hleTwo, a, ⟨ha, haTwo⟩, haUnique⟩ :=
    massDefect_structure components size s hpositive hmass hmassOne
  obtain ⟨b, ⟨hb, hbDef⟩, hbUnique⟩ :=
    existsUnique_eq_one_of_sum_eq_one components
      (fun x => size x + 1 - span x) hspanOne
  have hbPos := hpositive b hb
  have hbLe := hleTwo b hb
  have hbSpanLe := hspan b hb
  have hbNotOne : size b ≠ 1 := by
    intro hbOne
    have hbSpan : span b = 1 := by omega
    exact hforbid b hb hbOne hbSpan
  have hbTwo : size b = 2 := by omega
  have hba : b = a := haUnique b ⟨hb, hbTwo⟩
  subst b
  have haSpan : span a = 2 := by omega
  refine ⟨a, ha, haTwo, haSpan, ?_⟩
  intro x hx hxa
  have hxPos := hpositive x hx
  have hxLe := hleTwo x hx
  have hxSize : size x = 1 := by
    by_contra hxNotOne
    have hxTwo : size x = 2 := by omega
    exact hxa (haUnique x ⟨hx, hxTwo⟩)
  have hxDefLe : size x + 1 - span x ≤ 1 := by
    calc
      size x + 1 - span x ≤
          ∑ z ∈ components, (size z + 1 - span z) :=
        Finset.single_le_sum
          (f := fun z => size z + 1 - span z)
          (fun _ _ => Nat.zero_le _) hx
      _ = 1 := hspanOne
  have hxDefNe : size x + 1 - span x ≠ 1 := by
    intro hxDef
    exact hxa (hbUnique x ⟨hx, hxDef⟩)
  have hxSpanLe := hspan x hx
  exact ⟨hxSize, by omega⟩

/-- Saturating the intervals upgrades the two mass-defect-two partitions to
their exact `(component size, interval span)` shapes. -/
theorem massTwo_spanZero_structure
    {α : Type*} [DecidableEq α] (components : Finset α)
    (size span : α → ℕ) (s : ℕ)
    (hpositive : ∀ c ∈ components, 1 ≤ size c)
    (hmass : ∑ c ∈ components, size c = s)
    (hspan : ∀ c ∈ components, span c ≤ size c + 1)
    (hmassTwo : massDefect components s = 2)
    (hspanZero : spanDefect components size span = 0) :
    (∃ a ∈ components, size a = 3 ∧ span a = 4 ∧
        ∀ x ∈ components, x ≠ a → size x = 1 ∧ span x = 2) ∨
      (∃ a ∈ components, ∃ b ∈ components, a ≠ b ∧
        size a = 2 ∧ span a = 3 ∧
        size b = 2 ∧ span b = 3 ∧
        ∀ x ∈ components, x ≠ a → x ≠ b →
          size x = 1 ∧ span x = 2) := by
  have hsaturated := all_span_saturated_of_spanDefect_eq_zero
    components size span hspan hspanZero
  rcases massDefect_two_structure components size s hpositive hmass hmassTwo with
      hthree | htwo
  · left
    obtain ⟨a, ha, haThree, hothers⟩ := hthree
    refine ⟨a, ha, haThree, by rw [hsaturated a ha, haThree], ?_⟩
    intro x hx hxa
    have hxOne := hothers x hx hxa
    exact ⟨hxOne, by rw [hsaturated x hx, hxOne]⟩
  · right
    obtain ⟨a, ha, b, hb, hab, haTwo, hbTwo, hothers⟩ := htwo
    refine ⟨a, ha, b, hb, hab, haTwo,
      by rw [hsaturated a ha, haTwo], hbTwo,
      by rw [hsaturated b hb, hbTwo], ?_⟩
    intro x hx hxa hxb
    have hxOne := hothers x hx hxa hxb
    exact ⟨hxOne, by rw [hsaturated x hx, hxOne]⟩

/-- The `(mass,span)=(1,0)` allocation is one saturated size-two component
and saturated singleton components. -/
theorem massOne_spanZero_structure
    {α : Type*} [DecidableEq α] (components : Finset α)
    (size span : α → ℕ) (s : ℕ)
    (hpositive : ∀ c ∈ components, 1 ≤ size c)
    (hmass : ∑ c ∈ components, size c = s)
    (hspan : ∀ c ∈ components, span c ≤ size c + 1)
    (hmassOne : massDefect components s = 1)
    (hspanZero : spanDefect components size span = 0) :
    ∃ a ∈ components, size a = 2 ∧ span a = 3 ∧
      ∀ x ∈ components, x ≠ a → size x = 1 ∧ span x = 2 := by
  obtain ⟨hleTwo, a, ⟨ha, haTwo⟩, haUnique⟩ :=
    massDefect_structure components size s hpositive hmass hmassOne
  have hsaturated := all_span_saturated_of_spanDefect_eq_zero
    components size span hspan hspanZero
  refine ⟨a, ha, haTwo, by rw [hsaturated a ha, haTwo], ?_⟩
  intro x hx hxa
  have hxPos := hpositive x hx
  have hxLe := hleTwo x hx
  have hxOne : size x = 1 := by
    by_contra hxNotOne
    have hxTwo : size x = 2 := by omega
    exact hxa (haUnique x ⟨hx, hxTwo⟩)
  exact ⟨hxOne, by rw [hsaturated x hx, hxOne]⟩

/-- With both mass and span defects zero, every component is a saturated
singleton of interval span two. -/
theorem massZero_spanZero_structure
    {α : Type*} [DecidableEq α] (components : Finset α)
    (size span : α → ℕ) (s : ℕ)
    (hpositive : ∀ c ∈ components, 1 ≤ size c)
    (hmass : ∑ c ∈ components, size c = s)
    (hspan : ∀ c ∈ components, span c ≤ size c + 1)
    (hmassZero : massDefect components s = 0)
    (hspanZero : spanDefect components size span = 0) :
    ∀ c ∈ components, size c = 1 ∧ span c = 2 := by
  have hunit := massDefect_zero_forces_unit_sizes components size s
    hpositive hmass hmassZero
  have hsaturated := all_span_saturated_of_spanDefect_eq_zero
    components size span hspan hspanZero
  intro c hc
  have hcOne := hunit c hc
  exact ⟨hcOne, by rw [hsaturated c hc, hcOne]⟩

/-- Exact surviving pure-mass shape at total deficit two. -/
def PureMassShape
    {α : Type*} (components : Finset α)
    (size span : α → ℕ) (s unionCard : ℕ) : Prop := by
  classical
  exact massDefect components s = 2 ∧
  spanDefect components size span = 0 ∧
  overlapDefect components span unionCard = 0 ∧
  ((∃ a ∈ components, size a = 3 ∧ span a = 4 ∧
      ∀ x ∈ components, x ≠ a → size x = 1 ∧ span x = 2) ∨
    (∃ a ∈ components, ∃ b ∈ components, a ≠ b ∧
      size a = 2 ∧ span a = 3 ∧
      size b = 2 ∧ span b = 3 ∧
      ∀ x ∈ components, x ≠ a → x ≠ b →
        size x = 1 ∧ span x = 2))

/-- Exact surviving mixed mass-span shape at total deficit two. -/
def MassSpanShape
    {α : Type*} (components : Finset α)
    (size span : α → ℕ) (s unionCard : ℕ) : Prop := by
  classical
  exact massDefect components s = 1 ∧
  spanDefect components size span = 1 ∧
  overlapDefect components span unionCard = 0 ∧
  ∃ a ∈ components, size a = 2 ∧ span a = 2 ∧
    ∀ x ∈ components, x ≠ a → size x = 1 ∧ span x = 2

/-- Exact surviving mixed mass-overlap shape at total deficit two. -/
def MassOverlapShape
    {α : Type*} (components : Finset α)
    (size span : α → ℕ) (s unionCard : ℕ) : Prop := by
  classical
  exact massDefect components s = 1 ∧
  spanDefect components size span = 0 ∧
  overlapDefect components span unionCard = 1 ∧
  ∃ a ∈ components, size a = 2 ∧ span a = 3 ∧
    ∀ x ∈ components, x ≠ a → size x = 1 ∧ span x = 2

/-- Exact surviving pure-span shape at total deficit two. -/
def PureSpanShape
    {α : Type*} (components : Finset α)
    (size span : α → ℕ) (s unionCard : ℕ) : Prop := by
  classical
  exact massDefect components s = 0 ∧
  spanDefect components size span = 2 ∧
  overlapDefect components span unionCard = 0 ∧
  ∃ a ∈ components, size a = 1 ∧ span a = 0 ∧
    ∀ x ∈ components, x ≠ a → size x = 1 ∧ span x = 2

/-- Exact surviving pure-overlap shape at total deficit two. -/
def PureOverlapShape
    {α : Type*} (components : Finset α)
    (size span : α → ℕ) (s unionCard : ℕ) : Prop := by
  classical
  exact massDefect components s = 0 ∧
  spanDefect components size span = 0 ∧
  overlapDefect components span unionCard = 2 ∧
  ∀ c ∈ components, size c = 1 ∧ span c = 2

/-- Complete abstract five-shape classification after excluding singleton
span-one components.  The sixth aggregate allocation `(0,1,1)` is removed
constructively. -/
theorem twoDefect_five_shapes_of_no_unit_span_one
    {α : Type*} [DecidableEq α]
    (components : Finset α) (size span : α → ℕ) (s unionCard : ℕ)
    (hpositive : ∀ c ∈ components, 1 ≤ size c)
    (hmass : ∑ c ∈ components, size c = s)
    (hspan : ∀ c ∈ components, span c ≤ size c + 1)
    (hunion : unionCard ≤ ∑ c ∈ components, span c)
    (hforbid : ∀ c ∈ components, size c = 1 → span c = 1 → False)
    (hs : 1 ≤ s) (htwo : unionCard = 2 * s - 2) :
    PureMassShape components size span s unionCard ∨
      MassSpanShape components size span s unionCard ∨
      MassOverlapShape components size span s unionCard ∨
      PureSpanShape components size span s unionCard ∨
      PureOverlapShape components size span s unionCard := by
  rcases intervalDefect_two_six_cases components size span s unionCard
    hpositive hmass hspan hunion hs htwo with
    hpureMass | hmassSpan | hmassOverlap | hpureSpan |
      himpossible | hpureOverlap
  · left
    exact ⟨hpureMass.1, hpureMass.2.1, hpureMass.2.2,
      massTwo_spanZero_structure components size span s
        hpositive hmass hspan hpureMass.1 hpureMass.2.1⟩
  · right; left
    exact ⟨hmassSpan.1, hmassSpan.2.1, hmassSpan.2.2,
      massOne_spanOne_structure_of_no_unit_span_one
        components size span s hpositive hmass hspan hforbid
        hmassSpan.1 hmassSpan.2.1⟩
  · right; right; left
    exact ⟨hmassOverlap.1, hmassOverlap.2.1, hmassOverlap.2.2,
      massOne_spanZero_structure components size span s
        hpositive hmass hspan hmassOverlap.1 hmassOverlap.2.1⟩
  · right; right; right; left
    exact ⟨hpureSpan.1, hpureSpan.2.1, hpureSpan.2.2,
      pureSpanTwo_structure_of_no_unit_span_one
        components size span s hpositive hmass hspan hforbid
        hpureSpan.1 hpureSpan.2.1⟩
  · exact (massZero_spanOne_false_of_no_unit_span_one
      components size span s hpositive hmass hspan hforbid
      himpossible.1 himpossible.2.1).elim
  · right; right; right; right
    exact ⟨hpureOverlap.1, hpureOverlap.2.1, hpureOverlap.2.2,
      massZero_spanZero_structure components size span s
        hpositive hmass hspan hpureOverlap.1 hpureOverlap.2.1⟩

/-- Graph-instantiated sharp finite list for an all-nonbridge canonical
corridor of length `2s-2` in a properly two-colored graph. -/
theorem IsGeodesic.canonical_twoDefect_five_shapes
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ : V} {P : G.Walk w x₀}
    (color : G.Coloring Bool) (hP : IsGeodesic P)
    (hs : 1 ≤ slack P) (htwo : P.length = 2 * slack P - 2)
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
      PureMassShape components size span (slack P) unionCard ∨
        MassSpanShape components size span (slack P) unionCard ∨
        MassOverlapShape components size span (slack P) unionCard ∨
        PureSpanShape components size span (slack P) unionCard ∨
        PureOverlapShape components size span (slack P) unionCard := by
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
  have hunionValue : unionCard = 2 * slack P - 2 := by
    simp [unionCard, hunionEq, htwo]
  have hunionBound : unionCard ≤ ∑ C ∈ components, span C :=
    Finset.card_biUnion_le
  have hforbid : ∀ C ∈ components, size C = 1 → span C = 1 → False := by
    intro C _ hsizeC hspanC
    exact no_singleton_offCorridorComponent_span_one color P C
      (by simpa [size] using hsizeC)
      (by simpa [span, interval] using hspanC)
  refine ⟨components, by simp [components], ?_⟩
  simpa [size, span, interval, unionCard] using
    twoDefect_five_shapes_of_no_unit_span_one
      components size span (slack P) unionCard
      hpositive hmass hspan hunionBound hforbid hs hunionValue

/-- Number of indexed intervals containing a corridor coordinate. -/
noncomputable def coverMultiplicity
    {α β : Type*}
    (components : Finset α) (family : α → Finset β) (j : β) : ℕ := by
  classical
  exact (components.filter fun c => j ∈ family c).card

theorem coverMultiplicity_eq_card_filter
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (components : Finset α) (family : α → Finset β) (j : β) :
    coverMultiplicity components family j =
      (components.filter fun c => j ∈ family c).card := by
  classical
  unfold coverMultiplicity
  apply congrArg Finset.card
  ext c
  simp

/-- Exact finite double count: summing coordinate multiplicities equals the
sum of interval cardinalities when every interval lies in the universe. -/
theorem sum_coverMultiplicity_eq_sum_card
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (components : Finset α) (family : α → Finset β) (ground : Finset β)
    (hsubset : ∀ c ∈ components, family c ⊆ ground) :
    (∑ j ∈ ground, coverMultiplicity components family j) =
      ∑ c ∈ components, (family c).card := by
  calc
    (∑ j ∈ ground, coverMultiplicity components family j) =
        ∑ j ∈ ground, ∑ c ∈ components, if j ∈ family c then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          rw [coverMultiplicity_eq_card_filter]
          simp
    _ = ∑ c ∈ components, ∑ j ∈ ground,
          if j ∈ family c then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ c ∈ components, (family c).card := by
          apply Finset.sum_congr rfl
          intro c hc
          rw [Finset.sum_boole]
          apply congrArg Finset.card
          ext j
          simp
          exact fun hj => hsubset c hc hj

/-- If the indexed family covers its universe, every universe coordinate
has positive multiplicity. -/
theorem coverMultiplicity_pos_of_biUnion_eq
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (components : Finset α) (family : α → Finset β) (ground : Finset β)
    (hunion : components.biUnion family = ground) :
    ∀ j ∈ ground, 1 ≤ coverMultiplicity components family j := by
  intro j hj
  have hjUnion : j ∈ components.biUnion family := by simpa [hunion] using hj
  obtain ⟨c, hc, hjc⟩ := Finset.mem_biUnion.mp hjUnion
  rw [coverMultiplicity_eq_card_filter, Finset.one_le_card]
  exact ⟨c, by simp [hc, hjc]⟩

/-- Pointwise overlap identity.  Total interval cardinality minus covered
union cardinality is exactly the sum over coordinates of multiplicity minus
one. -/
theorem overlapDefect_eq_sum_multiplicityPred
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (components : Finset α) (family : α → Finset β) (ground : Finset β)
    (hunion : components.biUnion family = ground)
    (hsubset : ∀ c ∈ components, family c ⊆ ground) :
    overlapDefect components (fun c => (family c).card) ground.card =
      ∑ j ∈ ground, (coverMultiplicity components family j - 1) := by
  have hpositive := coverMultiplicity_pos_of_biUnion_eq
    components family ground hunion
  unfold overlapDefect
  rw [← sum_coverMultiplicity_eq_sum_card components family ground hsubset]
  rw [Finset.sum_tsub_distrib ground hpositive]
  simp

/-- Overlap defect two has either one coordinate of multiplicity three or
two distinct coordinates of multiplicity two, with multiplicity one at all
other covered coordinates. -/
theorem overlapDefect_two_multiplicity_cases
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (components : Finset α) (family : α → Finset β) (ground : Finset β)
    (hunion : components.biUnion family = ground)
    (hsubset : ∀ c ∈ components, family c ⊆ ground)
    (htwo : overlapDefect components (fun c => (family c).card)
      ground.card = 2) :
    (∃ j ∈ ground, coverMultiplicity components family j = 3 ∧
        ∀ k ∈ ground, k ≠ j → coverMultiplicity components family k = 1) ∨
      (∃ j ∈ ground, ∃ k ∈ ground, j ≠ k ∧
        coverMultiplicity components family j = 2 ∧
        coverMultiplicity components family k = 2 ∧
        ∀ x ∈ ground, x ≠ j → x ≠ k →
          coverMultiplicity components family x = 1) := by
  have hsum : ∑ j ∈ ground,
      (coverMultiplicity components family j - 1) = 2 := by
    rw [← overlapDefect_eq_sum_multiplicityPred
      components family ground hunion hsubset]
    exact htwo
  have hpositive := coverMultiplicity_pos_of_biUnion_eq
    components family ground hunion
  rcases sum_eq_two_cases ground
      (fun j => coverMultiplicity components family j - 1) hsum with
      hone | hpair
  · left
    obtain ⟨j, hj, hjdef, hothers⟩ := hone
    refine ⟨j, hj, by have := hpositive j hj; omega, ?_⟩
    intro k hk hkj
    have hkpos := hpositive k hk
    have hkzero := hothers k hk hkj
    omega
  · right
    obtain ⟨j, hj, k, hk, hjk, hjdef, hkdef, hothers⟩ := hpair
    refine ⟨j, hj, k, hk, hjk,
      by have := hpositive j hj; omega,
      by have := hpositive k hk; omega, ?_⟩
    intro x hx hxj hxk
    have hxpos := hpositive x hx
    have hxzero := hothers x hx hxj hxk
    omega

/-- Overlap defect one is one double-covered coordinate and multiplicity one
everywhere else in the covered universe. -/
theorem overlapDefect_one_multiplicity_structure
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (components : Finset α) (family : α → Finset β) (ground : Finset β)
    (hunion : components.biUnion family = ground)
    (hsubset : ∀ c ∈ components, family c ⊆ ground)
    (hone : overlapDefect components (fun c => (family c).card)
      ground.card = 1) :
    ∃! j, j ∈ ground ∧ coverMultiplicity components family j = 2 ∧
      ∀ k ∈ ground, k ≠ j → coverMultiplicity components family k = 1 := by
  have hsum : ∑ j ∈ ground,
      (coverMultiplicity components family j - 1) = 1 := by
    rw [← overlapDefect_eq_sum_multiplicityPred
      components family ground hunion hsubset]
    exact hone
  obtain ⟨j, ⟨hj, hjDef⟩, hjUnique⟩ :=
    existsUnique_eq_one_of_sum_eq_one ground
      (fun x => coverMultiplicity components family x - 1) hsum
  have hpositive := coverMultiplicity_pos_of_biUnion_eq
    components family ground hunion
  have hjTwo : coverMultiplicity components family j = 2 := by
    have := hpositive j hj
    omega
  have hothers : ∀ k ∈ ground, k ≠ j →
      coverMultiplicity components family k = 1 := by
    intro k hk hkj
    have hkPos := hpositive k hk
    have hkDefLe : coverMultiplicity components family k - 1 ≤ 1 := by
      calc
        coverMultiplicity components family k - 1 ≤
            ∑ x ∈ ground, (coverMultiplicity components family x - 1) :=
          Finset.single_le_sum
            (f := fun x => coverMultiplicity components family x - 1)
            (fun _ _ => Nat.zero_le _) hk
        _ = 1 := hsum
    have hkDefNe : coverMultiplicity components family k - 1 ≠ 1 := by
      intro hkDef
      exact hkj (hjUnique k ⟨hk, hkDef⟩)
    omega
  refine ⟨j, ⟨hj, hjTwo, hothers⟩, ?_⟩
  intro x hx
  rcases hx with ⟨hxGround, hxTwo, _⟩
  have hxDef : coverMultiplicity components family x - 1 = 1 := by
    omega
  exact hjUnique x ⟨hxGround, hxDef⟩

/-- Three length-two integer intervals through one coordinate force a second
coordinate to be covered at least twice.  This is the local obstruction that
rules out the abstract multiplicity-three branch at overlap defect two. -/
theorem lengthTwo_triple_forces_second_overlap
    {α : Type*} [DecidableEq α]
    (components : Finset α) (family : α → Finset ℕ) (lo : α → ℕ)
    (ground : Finset ℕ)
    (hsubset : ∀ c ∈ components, family c ⊆ ground)
    (hIco : ∀ c ∈ components, family c = Finset.Ico (lo c) (lo c + 2))
    {j : ℕ} (htriple : coverMultiplicity components family j = 3) :
    ∃ k ∈ ground, k ≠ j ∧
      2 ≤ coverMultiplicity components family k := by
  classical
  let covering := components.filter fun c => j ∈ family c
  have hcoveringCard : covering.card = 3 := by
    rw [coverMultiplicity_eq_card_filter] at htriple
    simpa [covering] using htriple
  have himageSubset : covering.image lo ⊆ Finset.Icc (j - 1) j := by
    intro l hl
    obtain ⟨c, hcCovering, rfl⟩ := Finset.mem_image.mp hl
    have hcData : c ∈ components ∧ j ∈ family c := by
      simpa [covering] using hcCovering
    rw [hIco c hcData.1] at hcData
    have hjBounds := Finset.mem_Ico.mp hcData.2
    simp only [Finset.mem_Icc]
    omega
  have himageCard : (covering.image lo).card ≤ 2 := by
    calc
      (covering.image lo).card ≤ (Finset.Icc (j - 1) j).card :=
        Finset.card_le_card himageSubset
      _ ≤ 2 := by simp; omega
  have himageLt : (covering.image lo).card < covering.card := by omega
  obtain ⟨a, haCovering, b, hbCovering, hab, hlo⟩ :=
    Finset.exists_ne_map_eq_of_card_image_lt himageLt
  have haData : a ∈ components ∧ j ∈ family a := by
    simpa [covering] using haCovering
  have hbData : b ∈ components ∧ j ∈ family b := by
    simpa [covering] using hbCovering
  have hjBounds : lo a ≤ j ∧ j < lo a + 2 := by
    rw [hIco a haData.1] at haData
    exact Finset.mem_Ico.mp haData.2
  have htwoCover {k : ℕ} (hka : k ∈ family a) (hkb : k ∈ family b) :
      2 ≤ coverMultiplicity components family k := by
    let pair : Finset α := {a, b}
    have hpairCard : pair.card = 2 := by simp [pair, hab]
    have hpairSubset : pair ⊆ components.filter fun c => k ∈ family c := by
      intro c hc
      have hcCases : c = a ∨ c = b := by simpa [pair] using hc
      rcases hcCases with rfl | rfl
      · simp [haData.1, hka]
      · simp [hbData.1, hkb]
    rw [coverMultiplicity_eq_card_filter]
    rw [← hpairCard]
    exact Finset.card_le_card hpairSubset
  by_cases hl : lo a = j
  · let k := j + 1
    have hka : k ∈ family a := by
      rw [hIco a haData.1, hl]
      simp [k]
    have hkb : k ∈ family b := by
      rw [hIco b hbData.1, ← hlo, hl]
      simp [k]
    exact ⟨k, hsubset a haData.1 hka, by simp [k], htwoCover hka hkb⟩
  · have hjEq : j = lo a + 1 := by omega
    let k := lo a
    have hka : k ∈ family a := by
      rw [hIco a haData.1]
      simp [k]
    have hkb : k ∈ family b := by
      rw [hIco b hbData.1, ← hlo]
      simp [k]
    exact ⟨k, hsubset a haData.1 hka, by simp [k, hjEq], htwoCover hka hkb⟩

/-- For literal length-two integer intervals, overlap defect two has exactly
two distinct double-covered coordinates.  The abstract single triple-covered
coordinate branch is unrealizable. -/
theorem overlapDefect_two_lengthTwo_structure
    {α : Type*} [DecidableEq α]
    (components : Finset α) (family : α → Finset ℕ) (lo : α → ℕ)
    (ground : Finset ℕ)
    (hunion : components.biUnion family = ground)
    (hsubset : ∀ c ∈ components, family c ⊆ ground)
    (hIco : ∀ c ∈ components, family c = Finset.Ico (lo c) (lo c + 2))
    (htwo : overlapDefect components (fun c => (family c).card)
      ground.card = 2) :
    ∃ j ∈ ground, ∃ k ∈ ground, j ≠ k ∧
      coverMultiplicity components family j = 2 ∧
      coverMultiplicity components family k = 2 ∧
      ∀ x ∈ ground, x ≠ j → x ≠ k →
        coverMultiplicity components family x = 1 := by
  rcases overlapDefect_two_multiplicity_cases components family ground
    hunion hsubset htwo with htriple | hpair
  · obtain ⟨j, hj, hjthree, hothers⟩ := htriple
    obtain ⟨k, hk, hkj, hktwo⟩ :=
      lengthTwo_triple_forces_second_overlap components family lo ground
        hsubset hIco hjthree
    have hkone := hothers k hk hkj
    omega
  · exact hpair

/-- A canonical off-corridor interval of cardinality two is literally an
integer interval `[l,l+2)`. -/
theorem offCorridorInterval_eq_Ico_of_card_eq_two
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ : V} (P : G.Walk w x₀)
    (C : OffCorridorComponent P)
    (hcard : (offCorridorComponentIntervalEdges P C).card = 2) :
    ∃ l : ℕ, offCorridorComponentIntervalEdges P C =
      Finset.Ico l (l + 2) := by
  classical
  let A := offCorridorAttachmentIndices P C
  by_cases hA : A.Nonempty
  · let l := A.min' hA
    let h := A.max' hA
    have hinterval : offCorridorComponentIntervalEdges P C =
        Finset.Ico l h := by
      simp [offCorridorComponentIntervalEdges, A, hA, l, h]
    have hcardIco : (Finset.Ico l h).card = 2 := by
      rw [← hinterval]
      exact hcard
    have hdiff : h - l = 2 := by
      simpa [Nat.card_Ico] using hcardIco
    have hh : h = l + 2 := by
      have hle := A.min'_le_max' hA
      omega
    exact ⟨l, by rw [hinterval, hh]⟩
  · have hempty : offCorridorComponentIntervalEdges P C = ∅ := by
      simp [offCorridorComponentIntervalEdges, A, hA]
    rw [hempty] at hcard
    simp at hcard

/-- In the canonical pure-overlap shape, the two units of overlap occur at
exactly two distinct corridor edges, each covered twice; every other edge is
covered once. -/
theorem canonical_pureOverlap_two_double_coordinates
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ : V} (P : G.Walk w x₀)
    (components : Finset (OffCorridorComponent P))
    (hunion : components.biUnion (offCorridorComponentIntervalEdges P) =
      Finset.range P.length)
    (hpure : PureOverlapShape components
      (fun C => (offCorridorComponentFinset C).card)
      (fun C => (offCorridorComponentIntervalEdges P C).card)
      (slack P) P.length) :
    ∃ j ∈ Finset.range P.length, ∃ k ∈ Finset.range P.length, j ≠ k ∧
      coverMultiplicity components (offCorridorComponentIntervalEdges P) j = 2 ∧
      coverMultiplicity components (offCorridorComponentIntervalEdges P) k = 2 ∧
      ∀ x ∈ Finset.range P.length, x ≠ j → x ≠ k →
        coverMultiplicity components (offCorridorComponentIntervalEdges P) x = 1 := by
  classical
  let family : OffCorridorComponent P → Finset ℕ :=
    offCorridorComponentIntervalEdges P
  have hsubset : ∀ C ∈ components, family C ⊆ Finset.range P.length := by
    intro C _ i hi
    exact offCorridorComponentIntervalEdges_subset_range P C hi
  have hIco : ∀ C ∈ components, ∃ l : ℕ,
      family C = Finset.Ico l (l + 2) := by
    intro C hC
    exact offCorridorInterval_eq_Ico_of_card_eq_two P C (hpure.2.2.2 C hC).2
  let lo : OffCorridorComponent P → ℕ := fun C =>
    if hC : C ∈ components then Classical.choose (hIco C hC) else 0
  have hIco' : ∀ C ∈ components, family C =
      Finset.Ico (lo C) (lo C + 2) := by
    intro C hC
    simpa [lo, hC] using Classical.choose_spec (hIco C hC)
  apply overlapDefect_two_lengthTwo_structure components family lo
    (Finset.range P.length)
  · simpa [family] using hunion
  · exact hsubset
  · exact hIco'
  · simpa [family] using hpure.2.2.1

/-- In the canonical mixed mass-overlap shape, exactly one corridor edge is
double-covered and every other corridor edge is covered once. -/
theorem canonical_massOverlap_unique_double_coordinate
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ : V} (P : G.Walk w x₀)
    (components : Finset (OffCorridorComponent P))
    (hunion : components.biUnion (offCorridorComponentIntervalEdges P) =
      Finset.range P.length)
    (hmixed : MassOverlapShape components
      (fun C => (offCorridorComponentFinset C).card)
      (fun C => (offCorridorComponentIntervalEdges P C).card)
      (slack P) P.length) :
    ∃! j, j ∈ Finset.range P.length ∧
      coverMultiplicity components (offCorridorComponentIntervalEdges P) j = 2 ∧
      ∀ k ∈ Finset.range P.length, k ≠ j →
        coverMultiplicity components (offCorridorComponentIntervalEdges P) k = 1 := by
  classical
  let family : OffCorridorComponent P → Finset ℕ :=
    offCorridorComponentIntervalEdges P
  have hsubset : ∀ C ∈ components, family C ⊆ Finset.range P.length := by
    intro C _ i hi
    exact offCorridorComponentIntervalEdges_subset_range P C hi
  apply overlapDefect_one_multiplicity_structure components family
    (Finset.range P.length)
  · simpa [family] using hunion
  · exact hsubset
  · simpa [family] using hmixed.2.2.1

/-- Uniform graph landing for an aligned near-boundary layer profile whose
adjacent extra-layer interaction is at most two.  The left and right extras
at gap `r` are the layer cardinalities minus the one corridor vertex. -/
theorem totalCost_le_rlBudget_of_nearBoundary_adjacentExtras
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (w x₀ : V) (m₁ m₂ : I → V) (level : V → ℕ)
    (s d : ℕ) (leftExtra rightExtra : Fin d → ℕ)
    (hs : 4 ≤ s) (hrow : d = 2 * s - 1 ∨ d = 2 * s - 2)
    (hweight : (∑ r : Fin d, (leftExtra r + rightExtra r)) ≤ 2 * s)
    (hadjacent : (∑ r : Fin d, (leftExtra r * rightExtra r)) ≤ 2)
    (hstep : ∀ {u v : V}, G.Adj u v →
      Nat.dist (level u) (level v) = 1)
    (hlayerLeft : ∀ r : Fin d,
      (levelLayer level r.1).card = leftExtra r + 1)
    (hlayerRight : ∀ r : Fin d,
      (levelLayer level (r.1 + 1)).card = rightExtra r + 1)
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
  let capacity : Fin d → ℕ := fun r =>
    leftExtra r + rightExtra r + leftExtra r * rightExtra r
  let weight : Fin d → ℕ := fun r => leftExtra r + rightExtra r
  have hcapacity : ∀ r, capacity r ≤ (weight r) ^ 2 := by
    intro r
    exact adjacentExtraCapacity_le_sum_sq (leftExtra r) (rightExtra r)
  have hcapacityEq : (∑ r : Fin d, capacity r) =
      (∑ r : Fin d, (leftExtra r + rightExtra r)) +
        (∑ r : Fin d, (leftExtra r * rightExtra r)) := by
    simp only [capacity, Finset.sum_add_distrib]
  have hcapacitySum : (∑ r : Fin d, capacity r) ≤ 2 * s + 2 := by
    rw [hcapacityEq]
    omega
  have hcut : ∀ r : Fin d,
      cutSize G (levelUpperCut level r.1) ≤ capacity r + 1 := by
    intro r
    have hproduct := cutSize_levelUpperCut_le_layerProduct level hstep r.1
    rw [hlayerLeft r, hlayerRight r] at hproduct
    dsimp [capacity]
    nlinarith
  apply totalCost_le_rlBudget_of_nearBoundaryCapacityProfile
    w x₀ m₁ m₂ level s d capacity weight hs hrow hcapacity
  · simpa [weight] using hweight
  · exact hcapacitySum
  · exact hroot
  · exact hstub
  · exact hendpoint₁
  · exact hendpoint₂
  · exact haligned
  · exact hRFC
  · exact hcut
  · exact hlegal

/-- A capacity profile with at most two non-baseline columns, each bounded
by three, has the exact aggregate bounds used by every canonical
`d = 2s-2` macro-block.  The quadratic term is an ordered-pair sum, hence
the two exceptional columns contribute at most `2 * 2^2 = 8`. -/
theorem twoHighColumns_profile_bounds
    {R : Type*} [Fintype R] [DecidableEq R]
    (capacity : R → ℕ) (high : Finset R)
    (hhigh : high.card ≤ 2)
    (hcapacity : ∀ r, capacity r ≤ if r ∈ high then 3 else 1) :
    (∑ r : R, capacity r) ≤ Fintype.card R + 4 ∧
      (∑ r : R, ∑ q : R, min (capacity r) (capacity q)) ≤
        (Fintype.card R) ^ 2 + 8 := by
  classical
  let indicator : R → ℕ := fun r => if r ∈ high then 1 else 0
  have hindicator (r : R) : indicator r ≤ 1 := by
    by_cases hr : r ∈ high <;> simp [indicator, hr]
  have hindicatorSum : (∑ r : R, indicator r) = high.card := by
    simp [indicator]
  have hcap' (r : R) : capacity r ≤ 1 + 2 * indicator r := by
    by_cases hr : r ∈ high <;>
      simpa [indicator, hr, Nat.add_comm] using hcapacity r
  have hlinear : (∑ r : R, capacity r) ≤ Fintype.card R + 4 := by
    calc
      (∑ r : R, capacity r) ≤ ∑ r : R, (1 + 2 * indicator r) :=
        Finset.sum_le_sum fun r _ => hcap' r
      _ = Fintype.card R + 2 * high.card := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
          mul_one]
        rw [← Finset.mul_sum, hindicatorSum]
      _ ≤ Fintype.card R + 4 := by omega
  have hpair (r q : R) : min (capacity r) (capacity q) ≤
      1 + 2 * (indicator r * indicator q) := by
    by_cases hr : r ∈ high <;> by_cases hq : q ∈ high
    · have hrCap := hcapacity r
      have hmin := (min_le_left (capacity r) (capacity q)).trans hrCap
      simpa [indicator, hr, hq] using hmin
    · have hqCap := hcapacity q
      have hmin := (min_le_right (capacity r) (capacity q)).trans hqCap
      simpa [indicator, hr, hq] using hmin
    · have hrCap := hcapacity r
      have hmin := (min_le_left (capacity r) (capacity q)).trans hrCap
      simpa [indicator, hr, hq] using hmin
    · have hrCap := hcapacity r
      have hmin := (min_le_left (capacity r) (capacity q)).trans hrCap
      simpa [indicator, hr, hq] using hmin
  have hproductSum :
      (∑ r : R, ∑ q : R, indicator r * indicator q) =
        (high.card) ^ 2 := by
    calc
      (∑ r : R, ∑ q : R, indicator r * indicator q) =
          ∑ r : R, indicator r * (∑ q : R, indicator q) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.mul_sum]
      _ = (∑ r : R, indicator r) * (∑ q : R, indicator q) := by
        rw [Finset.sum_mul]
      _ = (high.card) ^ 2 := by rw [hindicatorSum]; ring
  have hones : (∑ _r : R, ∑ _q : R, 1) =
      (Fintype.card R) ^ 2 := by simp [pow_two]
  have htwos :
      (∑ r : R, ∑ q : R, 2 * (indicator r * indicator q)) =
        2 * (high.card) ^ 2 := by
    calc
      (∑ r : R, ∑ q : R, 2 * (indicator r * indicator q)) =
          2 * (∑ r : R, ∑ q : R, indicator r * indicator q) := by
        symm
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.mul_sum]
      _ = 2 * (high.card) ^ 2 := by rw [hproductSum]
  have hquadratic :
      (∑ r : R, ∑ q : R, min (capacity r) (capacity q)) ≤
        (Fintype.card R) ^ 2 + 8 := by
    calc
      (∑ r : R, ∑ q : R, min (capacity r) (capacity q)) ≤
          ∑ r : R, ∑ q : R,
            (1 + 2 * (indicator r * indicator q)) := by
        exact Finset.sum_le_sum fun r _ =>
          Finset.sum_le_sum fun q _ => hpair r q
      _ = (Fintype.card R) ^ 2 + 2 * (high.card) ^ 2 := by
        calc
          (∑ r : R, ∑ q : R,
              (1 + 2 * (indicator r * indicator q))) =
              ∑ r : R, ((∑ _q : R, 1) +
                (∑ q : R, 2 * (indicator r * indicator q))) := by
            apply Finset.sum_congr rfl
            intro r _
            rw [Finset.sum_add_distrib]
          _ = (∑ _r : R, ∑ _q : R, 1) +
              (∑ r : R, ∑ q : R,
                2 * (indicator r * indicator q)) := by
            rw [Finset.sum_add_distrib]
          _ = (Fintype.card R) ^ 2 + 2 * (high.card) ^ 2 := by
            rw [hones, htwos]
      _ ≤ (Fintype.card R) ^ 2 + 8 := by
        have hsq := Nat.pow_le_pow_left hhigh 2
        norm_num at hsq ⊢
        omega
  exact ⟨hlinear, hquadratic⟩

/-- Finite-corridor specialization of `twoHighColumns_profile_bounds`. -/
theorem twoHighColumns_fin_profile_bounds
    (d : ℕ) (capacity : Fin d → ℕ) (high : Finset (Fin d))
    (hhigh : high.card ≤ 2)
    (hcapacity : ∀ r, capacity r ≤ if r ∈ high then 3 else 1) :
    (∑ r : Fin d, capacity r) ≤ d + 4 ∧
      (∑ r : Fin d, ∑ q : Fin d, min (capacity r) (capacity q)) ≤
        d ^ 2 + 8 := by
  simpa using twoHighColumns_profile_bounds capacity high hhigh hcapacity

/-- A baseline corridor whose residual columns are all at most one has
linear aggregate at most `d` and ordered-pair minimum aggregate at most
`d^2`.  This is the exact profile when the pure-span leaf is attached at
the stub and therefore lies in BFS level `d+1`. -/
theorem baselineColumns_fin_profile_bounds
    (d : ℕ) (capacity : Fin d → ℕ)
    (hcapacity : ∀ r, capacity r ≤ 1) :
    (∑ r : Fin d, capacity r) ≤ d ∧
      (∑ r : Fin d, ∑ q : Fin d, min (capacity r) (capacity q)) ≤
        d ^ 2 := by
  constructor
  · calc
      (∑ r : Fin d, capacity r) ≤ ∑ _r : Fin d, 1 :=
        Finset.sum_le_sum fun r _ => hcapacity r
      _ = d := by simp
  · calc
      (∑ r : Fin d, ∑ q : Fin d, min (capacity r) (capacity q)) ≤
          ∑ _r : Fin d, ∑ _q : Fin d, 1 := by
        exact Finset.sum_le_sum fun r _ =>
          Finset.sum_le_sum fun q _ =>
            (min_le_left (capacity r) (capacity q)).trans (hcapacity r)
      _ = d ^ 2 := by simp [pow_two]

/-- Any family of exceptional demands supported by one residual-unit cut
contains at most one member.  This is the exact RFC charging statement used
for the pendant leaf and for the chordless saturated size-three block. -/
theorem rootedCutCondition_atMostOne_cutSupported_exception
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (m₁ m₂ : I → V) (w x₀ : V)
    (hRFC : ∀ T : Finset V, w ∉ T →
      (∑ i : I, separationDemand T (m₁ i) (m₂ i)) +
        (if x₀ ∈ T then 1 else 0) ≤ cutSize G T)
    (T : Finset V) (exceptional : I → Prop) [DecidablePred exceptional]
    (hroot : w ∉ T)
    (hresidual : cutSize G T ≤ (if x₀ ∈ T then 1 else 0) + 1)
    (hsupported : ∀ i, exceptional i → Separates T (m₁ i) (m₂ i)) :
    ((Finset.univ : Finset I).filter exceptional).card ≤ 1 := by
  classical
  have hload : (∑ i : I, separationDemand T (m₁ i) (m₂ i)) ≤ 1 := by
    have h := hRFC T hroot
    omega
  have hcardEq : ((Finset.univ : Finset I).filter exceptional).card =
      ∑ i ∈ (Finset.univ : Finset I).filter exceptional,
        separationDemand T (m₁ i) (m₂ i) := by
    calc
      ((Finset.univ : Finset I).filter exceptional).card =
          ∑ _i ∈ (Finset.univ : Finset I).filter exceptional, 1 := by simp
      _ = ∑ i ∈ (Finset.univ : Finset I).filter exceptional,
          separationDemand T (m₁ i) (m₂ i) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hiExceptional : exceptional i := (Finset.mem_filter.mp hi).2
        symm
        exact (separationDemand_eq_one_iff T (m₁ i) (m₂ i)).2
          (hsupported i hiExceptional)
  rw [hcardEq]
  exact (Finset.sum_le_sum_of_subset (Finset.filter_subset exceptional
    (Finset.univ : Finset I))).trans hload

/-- Singleton-cut version of the residual-unit charging lemma.  A genuine
pendant vertex distinct from the root and stub has cut size one, so all
exceptional demands incident with it have total load at most one. -/
theorem rootedCutCondition_atMostOne_pendant_exception
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (m₁ m₂ : I → V) (w x₀ z : V)
    (hRFC : ∀ T : Finset V, w ∉ T →
      (∑ i : I, separationDemand T (m₁ i) (m₂ i)) +
        (if x₀ ∈ T then 1 else 0) ≤ cutSize G T)
    (exceptional : I → Prop) [DecidablePred exceptional]
    (hzw : z ≠ w) (hzx₀ : z ≠ x₀)
    (hleaf : cutSize G {z} ≤ 1)
    (hsupported : ∀ i, exceptional i → Separates {z} (m₁ i) (m₂ i)) :
    ((Finset.univ : Finset I).filter exceptional).card ≤ 1 := by
  apply rootedCutCondition_atMostOne_cutSupported_exception
    m₁ m₂ w x₀ hRFC {z} exceptional
  · simpa using hzw.symm
  · simpa [hzx₀.symm] using hleaf
  · exact hsupported

/-- Arbitrary-capacity matrix bound with one exception whose entire scaled
quadratic surcharge is supplied explicitly.  Removing the exceptional row
costs at most four in the cardinality term; no assumption on its threshold
span is hidden in the theorem. -/
theorem totalCost_le_rlBudget_of_one_scaled_exception
    {I R : Type*} [Fintype I] [Fintype R]
    (D : I → ℕ) (cross : I → R → ℕ) (capacity : R → ℕ)
    (exceptional : I) (correction s d : ℕ)
    (hcross : ∀ i r, cross i r ≤ 1)
    (haligned : ∀ i, i ≠ exceptional → D i = ∑ r : R, cross i r)
    (hcolumn : ∀ r, (∑ i : I, cross i r) ≤ capacity r)
    (hlegal : ∀ i, 4 ≤ D i)
    (hcorrection :
      4 * (D exceptional + 1) ^ 2 ≤
        4 * ((∑ r : R, cross exceptional r) + 1) ^ 2 + correction)
    (henvelope :
      let Q := ∑ r : R, ∑ q : R, min (capacity r) (capacity q)
      let C := ∑ r : R, capacity r
      4 * Q + 9 * C + correction + 4 ≤ 4 * rlBudget s d) :
    (∑ i : I, (D i + 1) ^ 2) ≤ rlBudget s d := by
  classical
  let L : I → ℕ := fun i => ∑ r : R, cross i r
  let C := ∑ r : R, capacity r
  let Q := ∑ r : R, ∑ q : R, min (capacity r) (capacity q)
  let totalL := ∑ i : I, L i
  let totalLsq := ∑ i : I, (L i) ^ 2
  let baseCost := ∑ i : I, (L i + 1) ^ 2
  have hlinear : totalL ≤ C := by
    calc
      totalL = ∑ r : R, ∑ i : I, cross i r := by
        simp only [totalL, L]
        rw [Finset.sum_comm]
      _ ≤ ∑ r : R, capacity r :=
        Finset.sum_le_sum fun r _ => hcolumn r
      _ = C := rfl
  have hpair (r q : R) :
      (∑ i : I, cross i r * cross i q) ≤
        min (capacity r) (capacity q) := by
    exact pairLoad_le_minColumnCapacity
      (fun i => cross i r) (fun i => cross i q)
      (capacity r) (capacity q)
      (fun i => hcross i r) (fun i => hcross i q)
      (hcolumn r) (hcolumn q)
  have hsquare : totalLsq ≤ Q := by
    calc
      totalLsq = ∑ i : I, ∑ r : R, ∑ q : R,
          cross i r * cross i q := by
        dsimp [totalLsq, L]
        simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
      _ = ∑ r : R, ∑ q : R, ∑ i : I,
          cross i r * cross i q := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.sum_comm]
      _ ≤ ∑ r : R, ∑ q : R, min (capacity r) (capacity q) := by
        exact Finset.sum_le_sum fun r _ =>
          Finset.sum_le_sum fun q _ => hpair r q
      _ = Q := rfl
  have hother : 4 * ((Finset.univ : Finset I).erase exceptional).card ≤
      ∑ i ∈ (Finset.univ : Finset I).erase exceptional, L i := by
    calc
      4 * ((Finset.univ : Finset I).erase exceptional).card =
          ∑ _i ∈ (Finset.univ : Finset I).erase exceptional, 4 := by
            simp [Nat.mul_comm]
      _ ≤ ∑ i ∈ (Finset.univ : Finset I).erase exceptional, L i := by
        apply Finset.sum_le_sum
        intro i hi
        have hie : i ≠ exceptional := (Finset.mem_erase.mp hi).1
        simpa [L, haligned i hie] using hlegal i
  have hcard : 4 * Fintype.card I ≤ totalL + 4 := by
    have hdecomp :
        (∑ i ∈ (Finset.univ : Finset I).erase exceptional, L i) +
          L exceptional = totalL := by
      simpa [totalL] using Finset.sum_erase_add
        (Finset.univ : Finset I) L (Finset.mem_univ exceptional)
    have hcardDecomp :
        ((Finset.univ : Finset I).erase exceptional).card + 1 =
          Fintype.card I := by
      simpa using Finset.card_erase_add_one (Finset.mem_univ exceptional)
    omega
  have hbaseIdentity : 4 * baseCost =
      4 * totalLsq + 8 * totalL + 4 * Fintype.card I := by
    calc
      4 * baseCost = ∑ i : I, 4 * (L i + 1) ^ 2 := by
        rw [Finset.mul_sum]
      _ = ∑ i : I, (4 * (L i) ^ 2 + 8 * L i + 4) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 4 * totalLsq + 8 * totalL + 4 * Fintype.card I := by
        simp [totalLsq, totalL, Finset.sum_add_distrib,
          Finset.mul_sum, Nat.mul_comm]
  have hbase : 4 * baseCost ≤ 4 * Q + 9 * C + 4 := by
    rw [hbaseIdentity]
    nlinarith
  have hotherCost :
      (∑ i ∈ (Finset.univ : Finset I).erase exceptional,
          4 * (D i + 1) ^ 2) =
        ∑ i ∈ (Finset.univ : Finset I).erase exceptional,
          4 * (L i + 1) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [haligned i (Finset.mem_erase.mp hi).1]
  have hcostScaled : 4 * (∑ i : I, (D i + 1) ^ 2) ≤
      4 * baseCost + correction := by
    have hDdecomp :
        (∑ i ∈ (Finset.univ : Finset I).erase exceptional,
          4 * (D i + 1) ^ 2) + 4 * (D exceptional + 1) ^ 2 =
          4 * (∑ i : I, (D i + 1) ^ 2) := by
      rw [Finset.mul_sum]
      simpa using Finset.sum_erase_add (Finset.univ : Finset I)
        (fun i => 4 * (D i + 1) ^ 2) (Finset.mem_univ exceptional)
    have hLdecomp :
        (∑ i ∈ (Finset.univ : Finset I).erase exceptional,
          4 * (L i + 1) ^ 2) + 4 * (L exceptional + 1) ^ 2 =
          4 * baseCost := by
      rw [Finset.mul_sum]
      simpa [baseCost] using Finset.sum_erase_add (Finset.univ : Finset I)
        (fun i => 4 * (L i + 1) ^ 2) (Finset.mem_univ exceptional)
    have hcorr : 4 * (D exceptional + 1) ^ 2 ≤
        4 * (L exceptional + 1) ^ 2 + correction := by
      simpa [L] using hcorrection
    omega
  have hscaled : 4 * (∑ i : I, (D i + 1) ^ 2) ≤
      4 * Q + 9 * C + correction + 4 := by
    exact hcostScaled.trans (by nlinarith)
  have henv : 4 * Q + 9 * C + correction + 4 ≤
      4 * rlBudget s d := by
    simpa [Q, C] using henvelope
  have hfour := hscaled.trans henv
  omega

/-- Arbitrary-capacity matrix envelope with one `+2` alignment exception.
The exceptional demand still contributes to every threshold column, so the
bound loses only its exact quadratic correction, not its whole cost. -/
theorem totalCost_le_rlBudget_of_one_addTwo_exception
    {I R : Type*} [Fintype I] [Fintype R]
    (D : I → ℕ) (cross : I → R → ℕ) (capacity : R → ℕ)
    (exceptional : I) (s d : ℕ)
    (hcross : ∀ i r, cross i r ≤ 1)
    (haligned : ∀ i, i ≠ exceptional → D i = ∑ r : R, cross i r)
    (hexceptional : D exceptional ≤
      (∑ r : R, cross exceptional r) + 2)
    (hcolumn : ∀ r, (∑ i : I, cross i r) ≤ capacity r)
    (hlegal : ∀ i, 4 ≤ D i)
    (henvelope :
      let Q := ∑ r : R, ∑ q : R, min (capacity r) (capacity q)
      let C := ∑ r : R, capacity r
      let L := ∑ r : R, cross exceptional r
      4 * Q + 9 * C + 16 * L + 34 ≤ 4 * rlBudget s d) :
    (∑ i : I, (D i + 1) ^ 2) ≤ rlBudget s d := by
  classical
  let L : I → ℕ := fun i => ∑ r : R, cross i r
  let C := ∑ r : R, capacity r
  let Q := ∑ r : R, ∑ q : R, min (capacity r) (capacity q)
  let totalL := ∑ i : I, L i
  let totalLsq := ∑ i : I, (L i) ^ 2
  let baseCost := ∑ i : I, (L i + 1) ^ 2
  have hlinear : totalL ≤ C := by
    calc
      totalL = ∑ r : R, ∑ i : I, cross i r := by
        simp only [totalL, L]
        rw [Finset.sum_comm]
      _ ≤ ∑ r : R, capacity r :=
        Finset.sum_le_sum fun r _ => hcolumn r
      _ = C := rfl
  have hpair (r q : R) :
      (∑ i : I, cross i r * cross i q) ≤
        min (capacity r) (capacity q) := by
    exact pairLoad_le_minColumnCapacity
      (fun i => cross i r) (fun i => cross i q)
      (capacity r) (capacity q)
      (fun i => hcross i r) (fun i => hcross i q)
      (hcolumn r) (hcolumn q)
  have hsquare : totalLsq ≤ Q := by
    calc
      totalLsq = ∑ i : I, ∑ r : R, ∑ q : R,
          cross i r * cross i q := by
        dsimp [totalLsq, L]
        simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
      _ = ∑ r : R, ∑ q : R, ∑ i : I,
          cross i r * cross i q := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.sum_comm]
      _ ≤ ∑ r : R, ∑ q : R, min (capacity r) (capacity q) := by
        exact Finset.sum_le_sum fun r _ =>
          Finset.sum_le_sum fun q _ => hpair r q
      _ = Q := rfl
  have hLexc : 2 ≤ L exceptional := by
    have hD := hlegal exceptional
    have hexc : D exceptional ≤ L exceptional + 2 := by
      simpa [L] using hexceptional
    omega
  have hother : 4 * ((Finset.univ : Finset I).erase exceptional).card ≤
      ∑ i ∈ (Finset.univ : Finset I).erase exceptional, L i := by
    calc
      4 * ((Finset.univ : Finset I).erase exceptional).card =
          ∑ _i ∈ (Finset.univ : Finset I).erase exceptional, 4 := by
            simp [Nat.mul_comm]
      _ ≤ ∑ i ∈ (Finset.univ : Finset I).erase exceptional, L i := by
        apply Finset.sum_le_sum
        intro i hi
        have hie : i ≠ exceptional := (Finset.mem_erase.mp hi).1
        have hDi := hlegal i
        simpa [L, haligned i hie] using hDi
  have hcard : 4 * Fintype.card I ≤ totalL + 2 := by
    have hdecomp :
        (∑ i ∈ (Finset.univ : Finset I).erase exceptional, L i) +
          L exceptional = totalL := by
      simpa [totalL] using Finset.sum_erase_add
        (Finset.univ : Finset I) L (Finset.mem_univ exceptional)
    have hcardDecomp :
        ((Finset.univ : Finset I).erase exceptional).card + 1 =
          Fintype.card I := by
      simpa using Finset.card_erase_add_one (Finset.mem_univ exceptional)
    omega
  have hbaseIdentity : 4 * baseCost =
      4 * totalLsq + 8 * totalL + 4 * Fintype.card I := by
    calc
      4 * baseCost = ∑ i : I, 4 * (L i + 1) ^ 2 := by
        rw [Finset.mul_sum]
      _ = ∑ i : I, (4 * (L i) ^ 2 + 8 * L i + 4) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 4 * totalLsq + 8 * totalL + 4 * Fintype.card I := by
        simp [totalLsq, totalL, Finset.sum_add_distrib,
          Finset.mul_sum, Nat.mul_comm]
  have hbase : 4 * baseCost ≤ 4 * Q + 9 * C + 2 := by
    rw [hbaseIdentity]
    nlinarith
  have hotherCost :
      (∑ i ∈ (Finset.univ : Finset I).erase exceptional,
          (D i + 1) ^ 2) =
        ∑ i ∈ (Finset.univ : Finset I).erase exceptional,
          (L i + 1) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [haligned i (Finset.mem_erase.mp hi).1]
  have hexcCost : (D exceptional + 1) ^ 2 ≤
      (L exceptional + 1) ^ 2 + 4 * L exceptional + 8 := by
    have hexc : D exceptional ≤ L exceptional + 2 := by
      simpa [L] using hexceptional
    nlinarith
  have hcost : (∑ i : I, (D i + 1) ^ 2) ≤
      baseCost + 4 * L exceptional + 8 := by
    have hDdecomp :
        (∑ i ∈ (Finset.univ : Finset I).erase exceptional,
          (D i + 1) ^ 2) + (D exceptional + 1) ^ 2 =
          ∑ i : I, (D i + 1) ^ 2 := by
      simpa using Finset.sum_erase_add (Finset.univ : Finset I)
        (fun i => (D i + 1) ^ 2) (Finset.mem_univ exceptional)
    have hLdecomp :
        (∑ i ∈ (Finset.univ : Finset I).erase exceptional,
          (L i + 1) ^ 2) + (L exceptional + 1) ^ 2 = baseCost := by
      simpa [baseCost] using Finset.sum_erase_add (Finset.univ : Finset I)
        (fun i => (L i + 1) ^ 2) (Finset.mem_univ exceptional)
    omega
  have hscaled : 4 * (∑ i : I, (D i + 1) ^ 2) ≤
      4 * Q + 9 * C + 16 * L exceptional + 34 := by
    nlinarith
  have henv : 4 * Q + 9 * C + 16 * L exceptional + 34 ≤
      4 * rlBudget s d := by
    simpa [Q, C, L] using henvelope
  have hfour := hscaled.trans henv
  omega

/-- Exact polynomial envelope for the pure-span pendant exception at
`d=2s-2`.  The bounds `Q<=d^2+8`, `C<=d+4`, and `L<=d-2` are the literal
worst profile and right-tail span of that macro-block. -/
theorem pureSpan_addTwo_exception_envelope
    (s d Q C L : ℕ) (hs : 5 ≤ s) (hd : d = 2 * s - 2)
    (hQ : Q ≤ d ^ 2 + 8) (hC : C ≤ d + 4) (hL : L ≤ d - 2) :
    4 * Q + 9 * C + 16 * L + 34 ≤ 4 * rlBudget s d := by
  subst d
  have hp : partnerDistance (2 * s - 2) = 2 := by
    let t := s - 1
    have hsEq : s = t + 1 := by simp [t]; omega
    rw [hsEq]
    have hdEq : 2 * (t + 1) - 2 = 2 * t := by omega
    rw [hdEq]
    simp [partnerDistance]
  have hbudget : rlBudget s (2 * s - 2) = 5 * s ^ 2 + 2 * s := by
    let t := s - 1
    have hsEq : s = t + 1 := by simp [t]; omega
    rw [hsEq]
    have hdEq : 2 * (t + 1) - 2 = 2 * t := by omega
    rw [hdEq]
    have hp' : partnerDistance (2 * t) = 2 := by
      simp [partnerDistance]
    unfold rlBudget
    rw [hp']
    ring
  rw [hbudget]
  have hdadd : (2 * s - 2) + 2 = 2 * s := by omega
  have hC' : C ≤ 2 * s + 2 := by omega
  have hL' : L + 4 ≤ 2 * s := by omega
  have hpoly : 10 * s + 36 ≤ 4 * s ^ 2 := by
    nlinarith [sq_nonneg (2 * s - 3)]
  nlinarith

/-- The saturated size-three macro-block has one of two exceptional rows:
its demand distance is four and its threshold span is either zero or two.
In both cases the scaled surcharge over the aligned surrogate is at most
`96`; the general one-exception matrix theorem therefore loses exactly
`100`, including the four-unit cardinality term. -/
theorem totalCost_le_rlBudget_of_one_q3_exception
    {I R : Type*} [Fintype I] [Fintype R]
    (D : I → ℕ) (cross : I → R → ℕ) (capacity : R → ℕ)
    (exceptional : I) (s d : ℕ)
    (hcross : ∀ i r, cross i r ≤ 1)
    (haligned : ∀ i, i ≠ exceptional → D i = ∑ r : R, cross i r)
    (hq3 : D exceptional = 4 ∧
      ((∑ r : R, cross exceptional r) = 0 ∨
        (∑ r : R, cross exceptional r) = 2))
    (hcolumn : ∀ r, (∑ i : I, cross i r) ≤ capacity r)
    (hlegal : ∀ i, 4 ≤ D i)
    (henvelope :
      let Q := ∑ r : R, ∑ q : R, min (capacity r) (capacity q)
      let C := ∑ r : R, capacity r
      4 * Q + 9 * C + 100 ≤ 4 * rlBudget s d) :
    (∑ i : I, (D i + 1) ^ 2) ≤ rlBudget s d := by
  apply totalCost_le_rlBudget_of_one_scaled_exception
    D cross capacity exceptional 96 s d hcross haligned hcolumn hlegal
  · rcases hq3 with ⟨hD, hspan | hspan⟩ <;>
      simp [hD, hspan]
  · dsimp
    dsimp at henvelope
    omega

/-- Exact polynomial landing for a saturated size-three macro-block at
`d=2s-2`.  Its exceptional cost is local, while the remaining profile has
the same `Q<=d^2+8`, `C<=d+4` envelope as the pendant-leaf case. -/
theorem q3_exception_envelope
    (s d Q C : ℕ) (hs : 5 ≤ s) (hd : d = 2 * s - 2)
    (hQ : Q ≤ d ^ 2 + 8) (hC : C ≤ d + 4) :
    4 * Q + 9 * C + 100 ≤ 4 * rlBudget s d := by
  subst d
  have hp : partnerDistance (2 * s - 2) = 2 := by
    let t := s - 1
    have hsEq : s = t + 1 := by simp [t]; omega
    rw [hsEq]
    have hdEq : 2 * (t + 1) - 2 = 2 * t := by omega
    rw [hdEq]
    simp [partnerDistance]
  have hbudget : rlBudget s (2 * s - 2) = 5 * s ^ 2 + 2 * s := by
    let t := s - 1
    have hsEq : s = t + 1 := by simp [t]; omega
    rw [hsEq]
    have hdEq : 2 * (t + 1) - 2 = 2 * t := by omega
    rw [hdEq]
    have hp' : partnerDistance (2 * t) = 2 := by
      simp [partnerDistance]
    unfold rlBudget
    rw [hp']
    ring
  rw [hbudget]
  have hdadd : (2 * s - 2) + 2 = 2 * s := by omega
  have hC' : C ≤ 2 * s + 2 := by omega
  have hsSq := Nat.pow_le_pow_left hs 2
  have hsLin := Nat.mul_le_mul_left 22 hs
  norm_num at hsSq hsLin
  have hpoly : 166 ≤ 4 * s ^ 2 + 22 * s := by nlinarith
  nlinarith

/-- Complete arithmetic closure of the pendant-leaf profile once the graph
constructor supplies its unique exceptional row and the two-high-column
capacity description. -/
theorem totalCost_le_rlBudget_of_pureSpan_twoHighColumns
    {I : Type*} [Fintype I]
    (D : I → ℕ) (d s : ℕ) (cross : I → Fin d → ℕ)
    (capacity : Fin d → ℕ) (high : Finset (Fin d))
    (exceptional : I)
    (hs : 5 ≤ s) (hd : d = 2 * s - 2)
    (hcross : ∀ i r, cross i r ≤ 1)
    (haligned : ∀ i, i ≠ exceptional →
      D i = ∑ r : Fin d, cross i r)
    (hexceptional : D exceptional ≤
      (∑ r : Fin d, cross exceptional r) + 2)
    (hexceptionalSpan : (∑ r : Fin d, cross exceptional r) ≤ d - 2)
    (hcolumn : ∀ r, (∑ i : I, cross i r) ≤ capacity r)
    (hlegal : ∀ i, 4 ≤ D i)
    (hhigh : high.card ≤ 2)
    (hcapacity : ∀ r, capacity r ≤ if r ∈ high then 3 else 1) :
    (∑ i : I, (D i + 1) ^ 2) ≤ rlBudget s d := by
  have hprofile := twoHighColumns_fin_profile_bounds d capacity high
    hhigh hcapacity
  apply totalCost_le_rlBudget_of_one_addTwo_exception
    D cross capacity exceptional s d hcross haligned hexceptional hcolumn hlegal
  dsimp
  exact pureSpan_addTwo_exception_envelope s d
    (∑ r : Fin d, ∑ q : Fin d, min (capacity r) (capacity q))
    (∑ r : Fin d, capacity r)
    (∑ r : Fin d, cross exceptional r)
    hs hd hprofile.2 hprofile.1 hexceptionalSpan

/-- Polynomial landing for the terminal pure-span attachment.  Here the
leaf is in level `d+1`, its truncated threshold span can reach `d-1`, but
all `d` residual corridor columns stay at the baseline one. -/
theorem pureSpan_stub_exception_envelope
    (s d Q C L : ℕ) (hs : 5 ≤ s) (hd : d = 2 * s - 2)
    (hQ : Q ≤ d ^ 2) (hC : C ≤ d) (hL : L ≤ d - 1) :
    4 * Q + 9 * C + 16 * L + 34 ≤ 4 * rlBudget s d := by
  subst d
  have hp : partnerDistance (2 * s - 2) = 2 := by
    let t := s - 1
    have hsEq : s = t + 1 := by simp [t]; omega
    rw [hsEq]
    have hdEq : 2 * (t + 1) - 2 = 2 * t := by omega
    rw [hdEq]
    simp [partnerDistance]
  have hbudget : rlBudget s (2 * s - 2) = 5 * s ^ 2 + 2 * s := by
    let t := s - 1
    have hsEq : s = t + 1 := by simp [t]; omega
    rw [hsEq]
    have hdEq : 2 * (t + 1) - 2 = 2 * t := by omega
    rw [hdEq]
    have hp' : partnerDistance (2 * t) = 2 := by
      simp [partnerDistance]
    unfold rlBudget
    rw [hp']
    ring
  rw [hbudget]
  have hdadd : (2 * s - 2) + 2 = 2 * s := by omega
  have hC' : C + 2 ≤ 2 * s := by omega
  have hL' : L + 3 ≤ 2 * s := by omega
  have hfactor : 10 ≤ 4 * s := by omega
  have hpoly : 10 * s ≤ 4 * s ^ 2 := by
    simpa [pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.mul_le_mul_right s hfactor
  nlinarith

/-- Complete arithmetic closure of the terminal pure-span attachment.  The
exceptional row may exceed its truncated threshold span by two (the actual
constructor gives only one), and RFC charging supplies its uniqueness. -/
theorem totalCost_le_rlBudget_of_pureSpan_stubBaselineColumns
    {I : Type*} [Fintype I]
    (D : I → ℕ) (d s : ℕ) (cross : I → Fin d → ℕ)
    (capacity : Fin d → ℕ) (exceptional : I)
    (hs : 5 ≤ s) (hd : d = 2 * s - 2)
    (hcross : ∀ i r, cross i r ≤ 1)
    (haligned : ∀ i, i ≠ exceptional →
      D i = ∑ r : Fin d, cross i r)
    (hexceptional : D exceptional ≤
      (∑ r : Fin d, cross exceptional r) + 2)
    (hexceptionalSpan : (∑ r : Fin d, cross exceptional r) ≤ d - 1)
    (hcolumn : ∀ r, (∑ i : I, cross i r) ≤ capacity r)
    (hlegal : ∀ i, 4 ≤ D i)
    (hcapacity : ∀ r, capacity r ≤ 1) :
    (∑ i : I, (D i + 1) ^ 2) ≤ rlBudget s d := by
  have hprofile := baselineColumns_fin_profile_bounds d capacity hcapacity
  apply totalCost_le_rlBudget_of_one_addTwo_exception
    D cross capacity exceptional s d hcross haligned hexceptional hcolumn hlegal
  dsimp
  exact pureSpan_stub_exception_envelope s d
    (∑ r : Fin d, ∑ q : Fin d, min (capacity r) (capacity q))
    (∑ r : Fin d, capacity r)
    (∑ r : Fin d, cross exceptional r)
    hs hd hprofile.2 hprofile.1 hexceptionalSpan

/-- Complete arithmetic closure of the saturated size-three profile once
the graph constructor supplies its unique local exceptional row and the
two-high-column capacity description. -/
theorem totalCost_le_rlBudget_of_q3_twoHighColumns
    {I : Type*} [Fintype I]
    (D : I → ℕ) (d s : ℕ) (cross : I → Fin d → ℕ)
    (capacity : Fin d → ℕ) (high : Finset (Fin d))
    (exceptional : I)
    (hs : 5 ≤ s) (hd : d = 2 * s - 2)
    (hcross : ∀ i r, cross i r ≤ 1)
    (haligned : ∀ i, i ≠ exceptional →
      D i = ∑ r : Fin d, cross i r)
    (hq3 : D exceptional = 4 ∧
      ((∑ r : Fin d, cross exceptional r) = 0 ∨
        (∑ r : Fin d, cross exceptional r) = 2))
    (hcolumn : ∀ r, (∑ i : I, cross i r) ≤ capacity r)
    (hlegal : ∀ i, 4 ≤ D i)
    (hhigh : high.card ≤ 2)
    (hcapacity : ∀ r, capacity r ≤ if r ∈ high then 3 else 1) :
    (∑ i : I, (D i + 1) ^ 2) ≤ rlBudget s d := by
  have hprofile := twoHighColumns_fin_profile_bounds d capacity high
    hhigh hcapacity
  apply totalCost_le_rlBudget_of_one_q3_exception
    D cross capacity exceptional s d hcross haligned hq3 hcolumn hlegal
  dsimp
  exact q3_exception_envelope s d
    (∑ r : Fin d, ∑ q : Fin d, min (capacity r) (capacity q))
    (∑ r : Fin d, capacity r)
    hs hd hprofile.2 hprofile.1

#print axioms sum_eq_two_cases
#print axioms intervalDefect_two_six_cases
#print axioms massDefect_two_structure
#print axioms spanDefect_two_unit_structure
#print axioms pureSpanTwo_structure_of_no_unit_span_one
#print axioms massZero_spanOne_false_of_no_unit_span_one
#print axioms massOne_spanOne_structure_of_no_unit_span_one
#print axioms massTwo_spanZero_structure
#print axioms massOne_spanZero_structure
#print axioms massZero_spanZero_structure
#print axioms twoDefect_five_shapes_of_no_unit_span_one
#print axioms IsGeodesic.canonical_twoDefect_five_shapes
#print axioms sum_coverMultiplicity_eq_sum_card
#print axioms overlapDefect_eq_sum_multiplicityPred
#print axioms overlapDefect_two_multiplicity_cases
#print axioms overlapDefect_one_multiplicity_structure
#print axioms lengthTwo_triple_forces_second_overlap
#print axioms overlapDefect_two_lengthTwo_structure
#print axioms offCorridorInterval_eq_Ico_of_card_eq_two
#print axioms canonical_pureOverlap_two_double_coordinates
#print axioms canonical_massOverlap_unique_double_coordinate
#print axioms totalCost_le_rlBudget_of_nearBoundary_adjacentExtras
#print axioms twoHighColumns_fin_profile_bounds
#print axioms baselineColumns_fin_profile_bounds
#print axioms rootedCutCondition_atMostOne_cutSupported_exception
#print axioms rootedCutCondition_atMostOne_pendant_exception
#print axioms totalCost_le_rlBudget_of_one_scaled_exception
#print axioms totalCost_le_rlBudget_of_one_addTwo_exception
#print axioms pureSpan_addTwo_exception_envelope
#print axioms totalCost_le_rlBudget_of_pureSpan_twoHighColumns
#print axioms pureSpan_stub_exception_envelope
#print axioms totalCost_le_rlBudget_of_pureSpan_stubBaselineColumns
#print axioms totalCost_le_rlBudget_of_one_q3_exception
#print axioms q3_exception_envelope
#print axioms totalCost_le_rlBudget_of_q3_twoHighColumns

end Erdos23GapGBTwoDefect
