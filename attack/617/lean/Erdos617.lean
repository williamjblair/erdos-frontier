/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
Foundation module for the Erdős Problem 617 campaign.
https://www.erdosproblems.com/617

Erdős–Gyárfás: for r ≥ 3, every r-coloring of the edges of the complete graph
on r^2 + 1 vertices admits r + 1 vertices spanning at most r - 1 colors, i.e.
some (r+1)-set misses a color entirely.

This module fixes the campaign vocabulary (`MissesColor`, `Balanced`), proves
the monochromatic-clique exclusion, bridges to Mathlib's `SimpleGraph`
independent-set API via the color-class graphs `G_k` (`colorGraph`), and banks
the vertex-deletion / extension-demand frame (`attachSet`, `IsHittingSet`)
together with its counting corollary `Σ τ_k ≤ r^2`.  The conditional reduction
`r5_of_extension_demand` reduces the r = 5 case (26 vertices) to the demand
bound `Σ τ_k > 25`.

`Statement r` matches the shape of formal-conjectures' `erdos_617` (its inner
`∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k` is definitionally
`MissesColor coloring S k`), so a future bridge is a one-liner.
-/
import Mathlib

namespace Erdos617

variable {V : Type*} {r : ℕ}

/-! ### Basic vocabulary -/

/-- `S` misses color `k`: no edge inside `S` is colored `k`. -/
def MissesColor (coloring : Sym2 V → Fin r) (S : Finset V) (k : Fin r) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k

/-- The counterexample predicate for Erdős 617: a coloring is `Balanced` if
every `(r+1)`-set of vertices uses every one of the `r` colors on its inside
edges. -/
def Balanced (coloring : Sym2 V → Fin r) : Prop :=
  ∀ S : Finset V, S.card = r + 1 → ∀ k : Fin r, ¬ MissesColor coloring S k

instance decidableMissesColor [DecidableEq V] (coloring : Sym2 V → Fin r) (S : Finset V)
    (k : Fin r) : Decidable (MissesColor coloring S k) :=
  inferInstanceAs (Decidable (∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k))

instance decidableBalanced [Fintype V] [DecidableEq V] (coloring : Sym2 V → Fin r) :
    Decidable (Balanced coloring) :=
  inferInstanceAs
    (Decidable (∀ S : Finset V, S.card = r + 1 → ∀ k : Fin r, ¬ MissesColor coloring S k))

/-- Erdős 617 for the parameter `r`, in the shape of formal-conjectures'
`erdos_617`. -/
def Statement (r : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V], Fintype.card V = r ^ 2 + 1 →
    ∀ coloring : Sym2 V → Fin r,
      ∃ (S : Finset V) (k : Fin r), S.card = r + 1 ∧ MissesColor coloring S k

/-- A coloring fails to be balanced iff it admits a witness for Erdős 617. -/
theorem not_balanced_iff {coloring : Sym2 V → Fin r} :
    ¬ Balanced coloring ↔
      ∃ (S : Finset V) (k : Fin r), S.card = r + 1 ∧ MissesColor coloring S k := by
  constructor
  · intro h
    by_contra hex
    push Not at hex
    exact h fun S hS k => hex S k hS
  · rintro ⟨S, k, hS, hmiss⟩ hbal
    exact hbal S hS k hmiss

/-- `Statement r` says precisely that no coloring on `r^2 + 1` vertices is
balanced. -/
theorem statement_iff (r : ℕ) :
    Statement r ↔
      ∀ (V : Type) [Fintype V] [DecidableEq V], Fintype.card V = r ^ 2 + 1 →
        ∀ coloring : Sym2 V → Fin r, ¬ Balanced coloring := by
  constructor
  · intro h V _ _ hV coloring
    exact not_balanced_iff.mpr (h V hV coloring)
  · intro h V _ _ hV coloring
    exact not_balanced_iff.mp (h V hV coloring)

/-! ### Monochromatic-clique exclusion -/

/-- A balanced coloring admits no monochromatic `K_{r+1}` (for `r ≥ 2`): a
monochromatic `(r+1)`-clique in color `k` misses every other color, and
`r ≥ 2` provides one. -/
theorem Balanced.no_monochromatic_clique (hr : 2 ≤ r) {coloring : Sym2 V → Fin r}
    (hbal : Balanced coloring) {S : Finset V} (hS : S.card = r + 1) (k : Fin r) :
    ¬ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) = k := by
  intro hmono
  haveI : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr hr
  obtain ⟨j, hj⟩ := exists_ne k
  refine hbal S hS j fun u hu v hv huv => ?_
  rw [hmono u hu v hv huv]
  exact hj.symm

/-! ### Color-class graphs and the independence bridge -/

/-- The color-class graph `G_k`: two vertices are adjacent iff their edge is
colored `k`. -/
def colorGraph (coloring : Sym2 V → Fin r) (k : Fin r) : SimpleGraph V where
  Adj u v := u ≠ v ∧ coloring s(u, v) = k
  symm := by
    rintro u v ⟨huv, hc⟩
    exact ⟨huv.symm, by rwa [Sym2.eq_swap]⟩
  loopless := ⟨fun v hv => hv.1 rfl⟩

@[simp] theorem colorGraph_adj {coloring : Sym2 V → Fin r} {k : Fin r} {u v : V} :
    (colorGraph coloring k).Adj u v ↔ u ≠ v ∧ coloring s(u, v) = k :=
  Iff.rfl

instance [DecidableEq V] (coloring : Sym2 V → Fin r) (k : Fin r) :
    DecidableRel (colorGraph coloring k).Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ coloring s(u, v) = k))

/-- `S` misses color `k` iff `S` is an independent set of the color-class
graph `G_k`. -/
theorem missesColor_iff_isIndepSet {coloring : Sym2 V → Fin r} {S : Finset V} {k : Fin r} :
    MissesColor coloring S k ↔ (colorGraph coloring k).IsIndepSet (S : Set V) := by
  constructor
  · intro h u hu v hv huv hadj
    exact h u hu v hv huv hadj.2
  · intro h u hu v hv huv hcol
    exact h hu hv huv ⟨huv, hcol⟩

/-- Independence-number formulation: a coloring is balanced iff no color-class
graph has an independent set of size `r + 1`. -/
theorem balanced_iff_forall_not_isIndepSet {coloring : Sym2 V → Fin r} :
    Balanced coloring ↔
      ∀ (k : Fin r) (S : Finset V), S.card = r + 1 →
        ¬ (colorGraph coloring k).IsIndepSet (S : Set V) := by
  constructor
  · intro h k S hS hind
    exact h S hS k (missesColor_iff_isIndepSet.mpr hind)
  · intro h S hS k hmiss
    exact h k S hS (missesColor_iff_isIndepSet.mp hmiss)

/-- Independence-number formulation, `IsNIndepSet` form: a coloring is
balanced iff no color-class graph has an `(r+1)`-independent set. -/
theorem balanced_iff_forall_not_isNIndepSet {coloring : Sym2 V → Fin r} :
    Balanced coloring ↔
      ∀ (k : Fin r) (S : Finset V), ¬ (colorGraph coloring k).IsNIndepSet (r + 1) S := by
  rw [balanced_iff_forall_not_isIndepSet]
  constructor
  · intro h k S hS
    exact h k S hS.card_eq hS.isIndepSet
  · intro h k S hcard hind
    exact h k S ⟨hind, hcard⟩

/-! ### Vertex deletion -/

/-- The coloring induced on the vertices other than `w`. -/
def restrictColoring (coloring : Sym2 V → Fin r) (w : V) :
    Sym2 {v : V // v ≠ w} → Fin r :=
  fun e => coloring (e.map Subtype.val)

/-- Deleting a vertex preserves `Balanced`. -/
theorem Balanced.restrict {coloring : Sym2 V → Fin r} (hbal : Balanced coloring) (w : V) :
    Balanced (restrictColoring coloring w) := by
  intro S hS k hmiss
  refine hbal (S.map ⟨Subtype.val, Subtype.val_injective⟩)
    (by rw [Finset.card_map, hS]) k ?_
  intro u hu v hv huv
  rw [Finset.mem_map] at hu hv
  obtain ⟨u', hu', rfl⟩ := hu
  obtain ⟨v', hv', rfl⟩ := hv
  exact hmiss u' hu' v' hv' fun h => huv (congrArg _ h)

section Counting

variable [Fintype V] [DecidableEq V]

/-- Deleting a vertex drops the vertex count by one. -/
theorem card_restrictVertices (w : V) :
    Fintype.card {v : V // v ≠ w} = Fintype.card V - 1 := by
  rw [Fintype.card_subtype, Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ w), Finset.card_univ]

/-- On `r^2 + 1` vertices, deleting a vertex leaves `r^2` vertices. -/
theorem card_restrictVertices_eq_sq (w : V) (hcard : Fintype.card V = r ^ 2 + 1) :
    Fintype.card {v : V // v ≠ w} = r ^ 2 := by
  rw [card_restrictVertices, hcard, Nat.add_sub_cancel]

/-! ### Attachment sets and the extension demand -/

/-- `attachSet coloring w k`: the vertices `v ≠ w` whose edge to `w` is
colored `k`.  As `k` ranges over `Fin r` these partition `V \ {w}`. -/
def attachSet (coloring : Sym2 V → Fin r) (w : V) (k : Fin r) : Finset V :=
  (Finset.univ.erase w).filter fun v => coloring s(w, v) = k

@[simp] theorem mem_attachSet {coloring : Sym2 V → Fin r} {w v : V} {k : Fin r} :
    v ∈ attachSet coloring w k ↔ v ≠ w ∧ coloring s(w, v) = k := by
  simp [attachSet]

/-- Attachment sets of distinct colors are disjoint. -/
theorem attachSet_pairwise_disjoint (coloring : Sym2 V → Fin r) (w : V) {k l : Fin r}
    (hkl : k ≠ l) : Disjoint (attachSet coloring w k) (attachSet coloring w l) := by
  rw [Finset.disjoint_left]
  intro v hk hl
  rw [mem_attachSet] at hk hl
  exact hkl (hk.2.symm.trans hl.2)

/-- The attachment sets cover `V \ {w}`. -/
theorem biUnion_attachSet (coloring : Sym2 V → Fin r) (w : V) :
    Finset.univ.biUnion (attachSet coloring w) = Finset.univ.erase w := by
  ext v
  constructor
  · intro hv
    rw [Finset.mem_biUnion] at hv
    obtain ⟨k, -, hk⟩ := hv
    exact Finset.mem_erase.mpr ⟨(mem_attachSet.mp hk).1, Finset.mem_univ v⟩
  · intro hv
    rw [Finset.mem_biUnion]
    exact ⟨coloring s(w, v), Finset.mem_univ _,
      mem_attachSet.mpr ⟨(Finset.mem_erase.mp hv).1, rfl⟩⟩

/-- The attachment-set sizes sum to `|V| - 1`. -/
theorem sum_card_attachSet (coloring : Sym2 V → Fin r) (w : V) :
    ∑ k : Fin r, (attachSet coloring w k).card = Fintype.card V - 1 := by
  have hdisj : ∀ k ∈ (Finset.univ : Finset (Fin r)), ∀ l ∈ Finset.univ, k ≠ l →
      Disjoint (attachSet coloring w k) (attachSet coloring w l) :=
    fun k _ l _ hkl => attachSet_pairwise_disjoint coloring w hkl
  rw [← Finset.card_biUnion hdisj, biUnion_attachSet,
    Finset.card_erase_of_mem (Finset.mem_univ w), Finset.card_univ]

/-- Extension demand: in a balanced coloring, the attachment set `H_k` of `w`
meets every `r`-set `T` avoiding `w` that misses color `k` — otherwise
`{w} ∪ T` would be an `(r+1)`-set missing `k`. -/
theorem Balanced.attachSet_inter_nonempty {coloring : Sym2 V → Fin r}
    (hbal : Balanced coloring) (w : V) (k : Fin r) {T : Finset V}
    (hwT : w ∉ T) (hT : T.card = r) (hmiss : MissesColor coloring T k) :
    (attachSet coloring w k ∩ T).Nonempty := by
  by_contra hempty
  have hout : ∀ v ∈ T, v ≠ w → coloring s(w, v) ≠ k := by
    intro v hv hvw hcol
    exact hempty ⟨v, Finset.mem_inter.mpr ⟨mem_attachSet.mpr ⟨hvw, hcol⟩, hv⟩⟩
  refine hbal (insert w T) (by rw [Finset.card_insert_of_notMem hwT, hT]) k ?_
  intro u hu v hv huv hcol
  rw [Finset.mem_insert] at hu hv
  rcases hu with rfl | hu
  · rcases hv with rfl | hv
    · exact huv rfl
    · exact hout v hv (fun h => hwT (h ▸ hv)) hcol
  · rcases hv with rfl | hv
    · refine hout u hu (fun h => hwT (h ▸ hu)) ?_
      rwa [Sym2.eq_swap]
    · exact hmiss u hu v hv huv hcol

/-- Independence form of the extension demand: `H_k` meets every `r`-set
avoiding `w` that is independent in the color-class graph `G_k`. -/
theorem Balanced.attachSet_inter_nonempty_of_isIndepSet {coloring : Sym2 V → Fin r}
    (hbal : Balanced coloring) (w : V) (k : Fin r) {T : Finset V}
    (hwT : w ∉ T) (hT : T.card = r)
    (hind : (colorGraph coloring k).IsIndepSet (T : Set V)) :
    (attachSet coloring w k ∩ T).Nonempty :=
  hbal.attachSet_inter_nonempty w k hwT hT (missesColor_iff_isIndepSet.mpr hind)

/-! ### The counting corollary -/

/-- `B` is a hitting set for color `k` at `w`: it meets every `r`-set avoiding
`w` that misses color `k`. -/
def IsHittingSet (coloring : Sym2 V → Fin r) (w : V) (k : Fin r) (B : Finset V) : Prop :=
  ∀ T : Finset V, w ∉ T → T.card = r → MissesColor coloring T k → (B ∩ T).Nonempty

/-- In a balanced coloring every attachment set is a hitting set. -/
theorem Balanced.attachSet_isHittingSet {coloring : Sym2 V → Fin r}
    (hbal : Balanced coloring) (w : V) (k : Fin r) :
    IsHittingSet coloring w k (attachSet coloring w k) :=
  fun _T hwT hT hmiss => hbal.attachSet_inter_nonempty w k hwT hT hmiss

/-- Counting corollary: if `τ k` lower-bounds the size of every hitting set
for color `k` at `w` (within `V \ {w}`), then `Σ τ_k ≤ |V| - 1`. -/
theorem Balanced.sum_le_of_hitting_lower_bound {coloring : Sym2 V → Fin r}
    (hbal : Balanced coloring) (w : V) (τ : Fin r → ℕ)
    (hτ : ∀ k, ∀ B : Finset V, w ∉ B → IsHittingSet coloring w k B → τ k ≤ B.card) :
    ∑ k, τ k ≤ Fintype.card V - 1 :=
  calc ∑ k, τ k ≤ ∑ k, (attachSet coloring w k).card :=
        Finset.sum_le_sum fun k _ =>
          hτ k _ (fun h => (mem_attachSet.mp h).1 rfl) (hbal.attachSet_isHittingSet w k)
    _ = Fintype.card V - 1 := sum_card_attachSet coloring w

/-- On `r^2 + 1` vertices the counting corollary reads `Σ τ_k ≤ r^2`.  This is
the interface where per-color hitting-set numerics plug in. -/
theorem Balanced.sum_le_sq {coloring : Sym2 V → Fin r}
    (hbal : Balanced coloring) (hcard : Fintype.card V = r ^ 2 + 1) (w : V) (τ : Fin r → ℕ)
    (hτ : ∀ k, ∀ B : Finset V, w ∉ B → IsHittingSet coloring w k B → τ k ≤ B.card) :
    ∑ k, τ k ≤ r ^ 2 := by
  have h := hbal.sum_le_of_hitting_lower_bound w τ hτ
  rwa [hcard, Nat.add_sub_cancel] at h

end Counting

/-! ### Conditional reduction of the `r = 5` case -/

set_option linter.unusedDecidableInType false in
/-- Conditional reduction of Erdős 617 at `r = 5`: if in every balanced
coloring on 26 vertices some vertex `w` admits hitting-set lower bounds with
`Σ τ_k > 25`, then no balanced coloring on 26 vertices exists.  This is the
interface the LEMMA-A/B numerics plug into.

The `[DecidableEq V]` binder in the conclusion is redundant but kept for shape
parity with `Statement` and formal-conjectures' `erdos_617`. -/
theorem r5_of_extension_demand
    (hdemand : ∀ (V : Type) [Fintype V] [DecidableEq V], Fintype.card V = 26 →
      ∀ coloring : Sym2 V → Fin 5, Balanced coloring →
        ∃ (w : V) (τ : Fin 5 → ℕ),
          (∀ k, ∀ B : Finset V, w ∉ B → IsHittingSet coloring w k B → τ k ≤ B.card) ∧
            25 < ∑ k, τ k) :
    ∀ (V : Type) [Fintype V] [DecidableEq V], Fintype.card V = 26 →
      ∀ coloring : Sym2 V → Fin 5, ¬ Balanced coloring := by
  intro V _ _ hcard coloring hbal
  obtain ⟨w, τ, hτ, hgt⟩ := hdemand V hcard coloring hbal
  have hle : ∑ k, τ k ≤ 5 ^ 2 := hbal.sum_le_sq (by norm_num [hcard]) w τ hτ
  norm_num at hle
  omega

/-- The extension-demand hypothesis settles Erdős 617 at `r = 5` outright. -/
theorem statement_five_of_extension_demand
    (hdemand : ∀ (V : Type) [Fintype V] [DecidableEq V], Fintype.card V = 26 →
      ∀ coloring : Sym2 V → Fin 5, Balanced coloring →
        ∃ (w : V) (τ : Fin 5 → ℕ),
          (∀ k, ∀ B : Finset V, w ∉ B → IsHittingSet coloring w k B → τ k ≤ B.card) ∧
            25 < ∑ k, τ k) :
    Statement 5 := by
  intro V _ _ hV coloring
  norm_num at hV
  exact not_balanced_iff.mp (r5_of_extension_demand hdemand V hV coloring)

end Erdos617
