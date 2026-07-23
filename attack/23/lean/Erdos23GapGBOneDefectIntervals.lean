/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair, OpenAI Codex
-/
import ErdosProblems.Erdos23GapGBOneDefect
import ErdosProblems.Erdos23GapGBBinaryLayerAuto

/-!
# Erdős 23 G-B: finite interval profiles at one defect

Pure finite-set rigidity translating the mass-defect interval tiling into
its doubled-level profile.  No graph or demand hypothesis appears here.
-/

namespace Erdos23GapGBOneDefectIntervals

open scoped BigOperators
open Erdos23GapGBBinaryLayerAuto

def blockInterval {α : Type*} (lo len : α → ℕ) (c : α) : Finset ℕ :=
  Finset.Ico (lo c) (lo c + len c)

def blockInterior {α : Type*} (lo len : α → ℕ) (c : α) : Finset ℕ :=
  Finset.Ioo (lo c) (lo c + len c)

def interiorLevels {α : Type*} [DecidableEq α]
    (components : Finset α) (lo len : α → ℕ) : Finset ℕ :=
  components.biUnion (blockInterior lo len)

def midpointLevels {α : Type*} [DecidableEq α]
    (components : Finset α) (lo : α → ℕ) : Finset ℕ :=
  components.image fun c => lo c + 1

/-- Zero-one extra-layer profile associated to a finite set of doubled
levels. -/
def levelIndicator (E : Finset ℕ) {d : ℕ} (k : Fin (d + 1)) : ℕ :=
  if k.1 ∈ E then 1 else 0

/-- Natural extension of `levelIndicator`, matching the interface used by
the automatic binary-layer theorem. -/
def extendedLevelIndicator (E : Finset ℕ) (d k : ℕ) : ℕ :=
  if hk : k < d + 1 then levelIndicator E ⟨k, hk⟩ else 0

/-- Exact conversion from a doubled-level set with one adjacent pair to the
finite sums required by `Erdos23GapGBBinaryLayerAuto`. -/
theorem indicatorProfile_counts
    (E : Finset ℕ) (d s : ℕ)
    (hsub : E ⊆ Finset.range (d + 1)) (hcard : E.card = s)
    (hunique : ∃! r, r < d ∧ r ∈ E ∧ r + 1 ∈ E) :
    (∀ k : Fin (d + 1), levelIndicator E k ≤ 1) ∧
      (∑ k : Fin (d + 1), levelIndicator E k) = s ∧
      (∑ r : Fin d, binaryHigh (extendedLevelIndicator E d) r.1) = 1 := by
  classical
  have hbinary : ∀ k : Fin (d + 1), levelIndicator E k ≤ 1 := by
    intro k
    unfold levelIndicator
    split <;> omega
  have hsum : (∑ k : Fin (d + 1), levelIndicator E k) = s := by
    change (∑ k : Fin (d + 1), if k.1 ∈ E then (1 : ℕ) else 0) = s
    have hsumRange :
        (∑ k : Fin (d + 1), if k.1 ∈ E then (1 : ℕ) else 0) =
          ∑ k ∈ Finset.range (d + 1), if k ∈ E then 1 else 0 :=
      Fin.sum_univ_eq_sum_range (fun k => if k ∈ E then (1 : ℕ) else 0) (d + 1)
    rw [hsumRange]
    have hfilter : (Finset.range (d + 1)).filter (fun k => k ∈ E) = E := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · exact fun h => h.2
      · intro hk
        exact ⟨Finset.mem_range.mp (hsub hk), hk⟩
    rw [← Finset.sum_filter]
    rw [hfilter]
    simp [hcard]
  have hhighPoint : ∀ r : Fin d,
      binaryHigh (extendedLevelIndicator E d) r.1 =
        if r.1 ∈ E ∧ r.1 + 1 ∈ E then 1 else 0 := by
    intro r
    unfold binaryHigh extendedLevelIndicator levelIndicator
    have hr0 : r.1 < d + 1 := by omega
    have hr1 : r.1 + 1 < d + 1 := by omega
    simp [hr0, hr1]
    by_cases h0 : r.1 ∈ E <;> by_cases h1 : r.1 + 1 ∈ E <;>
      simp [h0, h1]
  obtain ⟨r₀, ⟨hr₀lt, hr₀E, hr₀1E⟩, hr₀unique⟩ := hunique
  have hfilter : (Finset.univ : Finset (Fin d)).filter
      (fun r => r.1 ∈ E ∧ r.1 + 1 ∈ E) = {⟨r₀, hr₀lt⟩} := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hr
      apply Fin.ext
      exact hr₀unique r.1 ⟨r.2, hr.1, hr.2⟩
    · intro hr
      have hrval : r.1 = r₀ := congrArg Fin.val hr
      simpa [hrval] using And.intro hr₀E hr₀1E
  have hhigh :
      (∑ r : Fin d, binaryHigh (extendedLevelIndicator E d) r.1) = 1 := by
    calc
      (∑ r : Fin d, binaryHigh (extendedLevelIndicator E d) r.1) =
          ∑ r : Fin d, if r.1 ∈ E ∧ r.1 + 1 ∈ E then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro r _
            exact hhighPoint r
      _ = ((Finset.univ : Finset (Fin d)).filter
          (fun r => r.1 ∈ E ∧ r.1 + 1 ∈ E)).card := by
            rw [← Finset.sum_filter]
            simp
      _ = 1 := by rw [hfilter]; simp
  exact ⟨hbinary, hsum, hhigh⟩

theorem blockInterior_subset_blockInterval
    {α : Type*} (lo len : α → ℕ) (c : α) :
    blockInterior lo len c ⊆ blockInterval lo len c := by
  intro x hx
  have h := Finset.mem_Ioo.mp hx
  exact Finset.mem_Ico.mpr ⟨h.1.le, h.2⟩

/-- Disjoint closed-open blocks have disjoint strict interiors. -/
theorem pairwiseDisjoint_blockInterior
    {α : Type*} [DecidableEq α]
    (components : Finset α) (lo len : α → ℕ)
    (hdisjoint : (↑components : Set α).PairwiseDisjoint
      (blockInterval lo len)) :
    (↑components : Set α).PairwiseDisjoint (blockInterior lo len) := by
  intro a ha b hb hab
  exact (hdisjoint ha hb hab).mono
    (blockInterior_subset_blockInterval lo len a)
    (blockInterior_subset_blockInterval lo len b)

/-- Mass-defect one: one length-three block and otherwise length-two blocks
tile `[0,2s-1)`.  Their strict interiors are exactly `s` doubled levels,
cover an endpoint of every level gap, and have one unique adjacent pair. -/
theorem massIntervalProfile
    {α : Type*} [DecidableEq α]
    (components : Finset α) (lo len : α → ℕ) (s : ℕ)
    (hunion : components.biUnion (blockInterval lo len) =
      Finset.range (2 * s - 1))
    (hdisjoint : (↑components : Set α).PairwiseDisjoint
      (blockInterval lo len))
    (hlen : ∀ c ∈ components, len c = 2 ∨ len c = 3)
    (hbig : ∃! c, c ∈ components ∧ len c = 3) :
    (interiorLevels components lo len).card = s ∧
      (∀ r < 2 * s - 1,
        r ∈ interiorLevels components lo len ∨
          r + 1 ∈ interiorLevels components lo len) ∧
      ∃! r, r < 2 * s - 1 ∧
        r ∈ interiorLevels components lo len ∧
        r + 1 ∈ interiorLevels components lo len := by
  classical
  obtain ⟨big, ⟨hbigMem, hbigLen⟩, hbigUnique⟩ := hbig
  let interval := blockInterval lo len
  let interior := blockInterior lo len
  let E := interiorLevels components lo len
  have hlenEq : ∀ c ∈ components, len c = if c = big then 3 else 2 := by
    intro c hc
    by_cases hcb : c = big
    · subst c
      simp [hbigLen]
    · have hcCases := hlen c hc
      rcases hcCases with hc2 | hc3
      · simp [hcb, hc2]
      · exact (hcb (hbigUnique c ⟨hc, hc3⟩)).elim
  have hcardInterval : ∀ c ∈ components, (interval c).card = len c := by
    intro c _
    simp [interval, blockInterval, Nat.card_Ico]
  have hsumLen : ∑ c ∈ components, len c = 2 * s - 1 := by
    have hcard := Finset.card_biUnion hdisjoint
    rw [hunion] at hcard
    simp only [Finset.card_range] at hcard
    rw [hcard]
    apply Finset.sum_congr rfl
    intro c hc
    exact (hcardInterval c hc).symm
  have hsumLenShape : ∑ c ∈ components, len c =
      2 * components.card + 1 := by
    calc
      (∑ c ∈ components, len c) =
          ∑ c ∈ components, (if c = big then 3 else 2) := by
            apply Finset.sum_congr rfl
            intro c hc
            exact hlenEq c hc
      _ = 2 * components.card + 1 := by
        rw [show (∑ c ∈ components, (if c = big then 3 else 2)) =
            ∑ c ∈ components, (2 + if c = big then 1 else 0) by
          apply Finset.sum_congr rfl
          intro c _
          split <;> simp_all]
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, smul_eq_mul]
        rw [Finset.sum_ite_eq']
        simp [hbigMem]
        omega
  have hcardComponents : components.card = s - 1 := by
    have hcardPos : 1 ≤ components.card :=
      Finset.card_pos.mpr ⟨big, hbigMem⟩
    rw [hsumLen] at hsumLenShape
    omega
  have hcardInterior : ∀ c ∈ components,
      (interior c).card = if c = big then 2 else 1 := by
    intro c hc
    have hlenC := hlenEq c hc
    simp [interior, blockInterior, Nat.card_Ioo, hlenC]
    split <;> omega
  have hinteriorDisjoint :
      (↑components : Set α).PairwiseDisjoint interior := by
    exact pairwiseDisjoint_blockInterior components lo len hdisjoint
  have hcardE : E.card = s := by
    have hcard := Finset.card_biUnion hinteriorDisjoint
    dsimp [E, interiorLevels]
    rw [hcard]
    calc
      (∑ c ∈ components, (interior c).card) =
          ∑ c ∈ components, (if c = big then 2 else 1) := by
            apply Finset.sum_congr rfl
            intro c hc
            exact hcardInterior c hc
      _ = components.card + 1 := by
        rw [show (∑ c ∈ components, (if c = big then 2 else 1)) =
            ∑ c ∈ components, (1 + if c = big then 1 else 0) by
          apply Finset.sum_congr rfl
          intro c _
          split <;> simp_all]
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, one_smul]
        rw [Finset.sum_ite_eq']
        simp [hbigMem]
      _ = s := by omega
  have hcover : ∀ r < 2 * s - 1, r ∈ E ∨ r + 1 ∈ E := by
    intro r hr
    have hrUnion : r ∈ components.biUnion interval := by
      rw [show components.biUnion interval = Finset.range (2 * s - 1) by
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
      have hlenC := hlen c hc
      simp [interval, blockInterval] at hrc
      rcases hlenC with h2 | h3 <;> omega
  have hbigInterior : interior big =
      Finset.Ioo (lo big) (lo big + 3) := by
    simp [interior, blockInterior, hbigLen]
  have hrlt : lo big + 1 < 2 * s - 1 := by
    have hmem : lo big + 1 ∈ components.biUnion interval := by
      exact Finset.mem_biUnion.mpr ⟨big, hbigMem, by
        simp [interval, blockInterval, hbigLen]⟩
    rw [show components.biUnion interval = Finset.range (2 * s - 1) by
      exact hunion] at hmem
    exact Finset.mem_range.mp hmem
  have hrE : lo big + 1 ∈ E :=
    Finset.mem_biUnion.mpr ⟨big, hbigMem, by
      simp [E, interiorLevels, interior, blockInterior, hbigLen]⟩
  have hr1E : lo big + 1 + 1 ∈ E :=
    Finset.mem_biUnion.mpr ⟨big, hbigMem, by
      simp [E, interiorLevels, interior, blockInterior, hbigLen]⟩
  refine ⟨hcardE, hcover, ?_⟩
  refine ⟨lo big + 1, ⟨hrlt, hrE, hr1E⟩, ?_⟩
  intro q hq
  rcases hq with ⟨_hqlt, hqE, hq1E⟩
  obtain ⟨c, hc, hqc⟩ := Finset.mem_biUnion.mp hqE
  obtain ⟨c', hc', hq1c'⟩ := Finset.mem_biUnion.mp hq1E
  have hcc' : c = c' := by
    by_contra hne
    have hd := hdisjoint hc hc' hne
    have hqInC : q ∈ blockInterval lo len c :=
      blockInterior_subset_blockInterval lo len c hqc
    have hqInC' : q ∈ blockInterval lo len c' := by
      have hb := Finset.mem_Ioo.mp hq1c'
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    exact (Finset.disjoint_left.mp hd hqInC hqInC').elim
  subst c'
  have hcLen : len c = 3 := by
    have hcCases := hlen c hc
    rcases hcCases with hc2 | hc3
    · have h0 : lo c < q ∧ q < lo c + len c :=
        Finset.mem_Ioo.mp hqc
      have h1 : lo c < q + 1 ∧ q + 1 < lo c + len c :=
        Finset.mem_Ioo.mp hq1c'
      rw [hc2] at h0 h1
      omega
    · exact hc3
  have hcbig : c = big := hbigUnique c ⟨hc, hcLen⟩
  subst c
  have hqBounds : lo big < q ∧ q < lo big + len big :=
    Finset.mem_Ioo.mp hqc
  have hq1Bounds : lo big < q + 1 ∧ q + 1 < lo big + len big :=
    Finset.mem_Ioo.mp hq1c'
  rw [hbigLen] at hqBounds hq1Bounds
  omega

/-- Overlap-defect one: `s` length-two intervals cover `[0,2s-1)`.
Their midpoints are distinct, give exactly `s` doubled levels, cover an
endpoint of every gap, and have one unique adjacent pair. -/
theorem overlapIntervalProfile
    {α : Type*} [DecidableEq α]
    (components : Finset α) (lo : α → ℕ) (s : ℕ)
    (hs : 1 ≤ s) (hcard : components.card = s)
    (hunion : components.biUnion
      (fun c => Finset.Ico (lo c) (lo c + 2)) =
        Finset.range (2 * s - 1)) :
    Set.InjOn lo (↑components : Set α) ∧
      (midpointLevels components lo).card = s ∧
      (∀ r < 2 * s - 1,
        r ∈ midpointLevels components lo ∨
          r + 1 ∈ midpointLevels components lo) ∧
      ∃! r, r < 2 * s - 1 ∧
        r ∈ midpointLevels components lo ∧
        r + 1 ∈ midpointLevels components lo := by
  classical
  let d := 2 * s - 1
  let E := midpointLevels components lo
  let P := E.image Nat.pred
  have hmidInterval : ∀ c ∈ components,
      lo c + 1 ∈ Finset.Ico (lo c) (lo c + 2) := by
    intro c _
    simp
  have hEpos : ∀ e ∈ E, 1 ≤ e := by
    intro e he
    obtain ⟨c, _hc, rfl⟩ := Finset.mem_image.mp he
    omega
  have hEsub : E ⊆ Finset.range d := by
    intro e he
    obtain ⟨c, hc, heq⟩ := Finset.mem_image.mp he
    subst e
    have hm : lo c + 1 ∈ components.biUnion
        (fun x => Finset.Ico (lo x) (lo x + 2)) :=
      Finset.mem_biUnion.mpr ⟨c, hc, hmidInterval c hc⟩
    rw [hunion] at hm
    exact hm
  have hcover : ∀ r < d, r ∈ E ∨ r + 1 ∈ E := by
    intro r hr
    have hrUnion : r ∈ components.biUnion
        (fun c => Finset.Ico (lo c) (lo c + 2)) := by
      rw [hunion]
      exact Finset.mem_range.mpr hr
    obtain ⟨c, hc, hrc⟩ := Finset.mem_biUnion.mp hrUnion
    have hb := Finset.mem_Ico.mp hrc
    have hcases : r = lo c ∨ r = lo c + 1 := by omega
    rcases hcases with hleft | hright
    · right
      exact Finset.mem_image.mpr ⟨c, hc, by omega⟩
    · left
      exact Finset.mem_image.mpr ⟨c, hc, by omega⟩
  have hPsub : P ⊆ Finset.range d := by
    intro r hr
    obtain ⟨e, he, her⟩ := Finset.mem_image.mp hr
    have heRange := Finset.mem_range.mp (hEsub he)
    subst r
    exact Finset.mem_range.mpr (lt_of_le_of_lt (Nat.pred_le e) heRange)
  have hrangeSub : Finset.range d ⊆ E ∪ P := by
    intro r hr
    have hrlt := Finset.mem_range.mp hr
    rcases hcover r hrlt with hrE | hr1E
    · exact Finset.mem_union_left P hrE
    · apply Finset.mem_union_right E
      exact Finset.mem_image.mpr ⟨r + 1, hr1E, by simp⟩
  have hunionEP : E ∪ P = Finset.range d :=
    Finset.Subset.antisymm
      (Finset.union_subset hEsub hPsub) hrangeSub
  have hpredInj : Set.InjOn Nat.pred (↑E : Set ℕ) := by
    intro a ha b hb hab
    have haPos := hEpos a ha
    have hbPos := hEpos b hb
    have haEq := Nat.succ_pred_eq_of_pos (by omega : 0 < a)
    have hbEq := Nat.succ_pred_eq_of_pos (by omega : 0 < b)
    omega
  have hcardP : P.card = E.card := by
    exact Finset.card_image_iff.mpr hpredInj
  have hcardEle : E.card ≤ s := by
    calc
      E.card = (components.image fun c => lo c + 1).card := rfl
      _ ≤ components.card := Finset.card_image_le
      _ = s := hcard
  have hcardUnion := Finset.card_union_add_card_inter E P
  have hcardE : E.card = s := by
    rw [hunionEP, Finset.card_range, hcardP] at hcardUnion
    dsimp [d] at hcardUnion
    omega
  have hinterCard : (E ∩ P).card = 1 := by
    rw [hunionEP, Finset.card_range, hcardP, hcardE] at hcardUnion
    dsimp [d] at hcardUnion
    omega
  obtain ⟨r, hinterEq⟩ := Finset.card_eq_one.mp hinterCard
  have hrData : r < d ∧ r ∈ E ∧ r + 1 ∈ E := by
    have hrInter : r ∈ E ∩ P := by simp [hinterEq]
    have hrE : r ∈ E := Finset.mem_inter.mp hrInter |>.1
    have hrP : r ∈ P := Finset.mem_inter.mp hrInter |>.2
    obtain ⟨e, heE, heq⟩ := Finset.mem_image.mp hrP
    have hePos := hEpos e heE
    have heSucc := Nat.succ_pred_eq_of_pos (by omega : 0 < e)
    have her : e = r + 1 := by omega
    have hrlt := Finset.mem_range.mp (hEsub hrE)
    exact ⟨hrlt, hrE, by simpa [her] using heE⟩
  have hloInj : Set.InjOn lo (↑components : Set α) := by
    have hmidCard : (components.image fun c => lo c + 1).card =
        components.card := by simpa [E, midpointLevels, hcard] using hcardE
    have hmidInj : Set.InjOn (fun c => lo c + 1)
        (↑components : Set α) := Finset.card_image_iff.mp hmidCard
    intro a ha b hb hab
    apply hmidInj ha hb
    exact congrArg (fun x => x + 1) hab
  refine ⟨hloInj, hcardE, hcover, r, hrData, ?_⟩
  intro q hq
  rcases hq with ⟨_hqlt, hqE, hq1E⟩
  have hqP : q ∈ P :=
    Finset.mem_image.mpr ⟨q + 1, hq1E, by simp⟩
  have hqInter : q ∈ E ∩ P := Finset.mem_inter.mpr ⟨hqE, hqP⟩
  simpa [hinterEq] using hqInter

#print axioms indicatorProfile_counts
#print axioms massIntervalProfile
#print axioms overlapIntervalProfile

end Erdos23GapGBOneDefectIntervals
