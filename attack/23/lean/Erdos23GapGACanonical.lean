/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair, OpenAI Codex
-/
import ErdosProblems.Erdos23GapGA

/-!
# Erdős 23, gap G-A: canonical graph construction

This file advances the graph-theoretic construction isolated as
`Erdos23GapGA.CanonicalChargeTheorem`.  It proves:

* the cut argument assigning every nonbridge corridor edge to a covering
  off-corridor component;
* strict monotonicity, up to orientation, of all common visits;
* the exact ride/excursion transition dichotomy and the bijection between
  unit transitions and actually ridden edges;
* extraction of the canonical component of every non-unit transition;
* pairwise disjointness and component-interval containment of all transition
  gap finsets;
* exact global and per-component ride/excursion cardinalities; and
* the repaired exceptional initial/final-tail inequality; and
* the complete `CanonicalChargeTheorem`.

The exceptional-tail proof uses a tightness contradiction: equality in the
component span and ride packing bounds would make both extreme interval edges
ridden, but the corresponding component attachments cannot consistently lie
in the initial/final tails of a geodesic.
-/

open scoped BigOperators

namespace Erdos23GapGA

open SimpleGraph

variable {V : Type*}

/-- The component of an off-corridor vertex. -/
noncomputable def offCorridorComponentOf
    [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (P : G.Walk u v) (x : V) (hx : x ∉ P.support) :
    OffCorridorComponent P :=
  G.componentComplMk (by simpa [supportFinset] using hx)

/-- Adjacent off-corridor vertices belong to the same canonical component. -/
theorem offCorridorComponentOf_eq_of_adj
    [DecidableEq V] {G : SimpleGraph V} {u v x y : V}
    (P : G.Walk u v) (hx : x ∉ P.support)
    (hy : y ∉ P.support) (hxy : G.Adj x y) :
    offCorridorComponentOf P x hx = offCorridorComponentOf P y hy := by
  apply G.componentComplMk_eq_of_adj _ _ hxy

/-- An off-corridor vertex lies in its canonical component. -/
theorem mem_offCorridorComponentOf
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v x : V}
    (P : G.Walk u v) (hx : x ∉ P.support) :
    x ∈ offCorridorComponentFinset (offCorridorComponentOf P x hx) := by
  apply (mem_offCorridorComponentFinset _).2
  exact G.componentComplMk_mem (by simpa [supportFinset] using hx)

/-- If an off-corridor vertex is adjacent to corridor coordinate `j`, then
`j` is an attachment index of its canonical component. -/
theorem attachment_mem_of_offCorridor_adj
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v x : V}
    (P : G.Walk u v) (hx : x ∉ P.support) {j : ℕ}
    (hj : j ≤ P.length) (hadj : G.Adj x (P.getVert j)) :
    j ∈ offCorridorAttachmentIndices P (offCorridorComponentOf P x hx) := by
  exact (mem_offCorridorAttachmentIndices _ _ _).2
    ⟨hj, x, mem_offCorridorComponentOf P hx, hadj⟩

/-- The corridor coordinate of `P.getVert j` is exactly `j` on a geodesic
and within the corridor range. -/
theorem IsGeodesic.support_idxOf_getVert
    [DecidableEq V] {G : SimpleGraph V} {u v : V}
    {P : G.Walk u v} (hP : IsGeodesic P) {j : ℕ} (hj : j ≤ P.length) :
    P.support.idxOf (P.getVert j) = j := by
  have hmem : P.getVert j ∈ P.support := P.getVert_mem_support j
  have hidx : P.support.idxOf (P.getVert j) ≤ P.length :=
    support_idxOf_le_length P hmem
  have hget := P.getVert_support_idxOf hmem
  exact hP.isPath.getVert_injOn hidx hj hget

/-- The left side associated to the corridor edge starting at `i`.

A corridor vertex is on the left precisely when its corridor coordinate is
at most `i`.  An off-corridor vertex is on the left precisely when its
canonical component has at least one attachment at a coordinate at most
`i`.  Components without a left attachment are placed on the right. -/
noncomputable def corridorLeftRegion
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (P : G.Walk u v) (i : ℕ) : Set V := by
  classical
  exact {x | if hx : x ∈ P.support then P.support.idxOf x ≤ i
    else ∃ j ∈ offCorridorAttachmentIndices P
      (offCorridorComponentOf P x hx), j ≤ i}

theorem mem_corridorLeftRegion_of_mem_support
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v x : V}
    (P : G.Walk u v) (i : ℕ) (hx : x ∈ P.support) :
    x ∈ corridorLeftRegion P i ↔ P.support.idxOf x ≤ i := by
  classical
  simp [corridorLeftRegion, hx]

theorem mem_corridorLeftRegion_of_not_mem_support
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v x : V}
    (P : G.Walk u v) (i : ℕ) (hx : x ∉ P.support) :
    x ∈ corridorLeftRegion P i ↔
      ∃ j ∈ offCorridorAttachmentIndices P
        (offCorridorComponentOf P x hx), j ≤ i := by
  classical
  simp [corridorLeftRegion, hx]

/-- Corridor coordinates at most `i` lie in the left region. -/
theorem IsGeodesic.getVert_mem_corridorLeftRegion
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v : V}
    {P : G.Walk u v} (hP : IsGeodesic P) {i j : ℕ}
    (hj : j ≤ P.length) (hji : j ≤ i) :
    P.getVert j ∈ corridorLeftRegion P i := by
  have hmem : P.getVert j ∈ P.support := P.getVert_mem_support j
  rw [mem_corridorLeftRegion_of_mem_support P i hmem]
  rw [hP.support_idxOf_getVert hj]
  exact hji

/-- Corridor coordinates strictly to the right of `i` do not lie in the
left region. -/
theorem IsGeodesic.getVert_not_mem_corridorLeftRegion
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v : V}
    {P : G.Walk u v} (hP : IsGeodesic P) {i j : ℕ}
    (hj : j ≤ P.length) (hij : i < j) :
    P.getVert j ∉ corridorLeftRegion P i := by
  have hmem : P.getVert j ∈ P.support := P.getVert_mem_support j
  rw [mem_corridorLeftRegion_of_mem_support P i hmem]
  rw [hP.support_idxOf_getVert hj]
  omega

/-- If no off-corridor attachment interval covers the edge `i`, every graph
edge crossing the associated left region is the corridor edge `i` itself.

This is the cut form of the alternate-path argument in the paper proof.  It
does not assume that an alternate path leaves and returns to the corridor
only once. -/
theorem corridorLeftRegion_crossing_eq
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v a b : V}
    {P : G.Walk u v} (hP : IsGeodesic P) {i : ℕ}
    (hno : ∀ C : OffCorridorComponent P,
      ¬offCorridorComponentCoversIndex P C i)
    (ha : a ∈ corridorLeftRegion P i)
    (hb : b ∉ corridorLeftRegion P i) (hab : G.Adj a b) :
    a = P.getVert i ∧ b = P.getVert (i + 1) := by
  classical
  by_cases haP : a ∈ P.support
  · have hai : P.support.idxOf a ≤ i :=
      (mem_corridorLeftRegion_of_mem_support P i haP).1 ha
    by_cases hbP : b ∈ P.support
    · have hib : i < P.support.idxOf b := by
        by_contra hnot
        exact hb ((mem_corridorLeftRegion_of_mem_support P i hbP).2 (by omega))
      have hdist : Nat.dist (P.support.idxOf a) (P.support.idxOf b) = 1 := by
        rw [← hP.dist_eq_natDist_support_idxOf haP hbP]
        exact dist_eq_one_iff_adj.mpr hab
      have hsucc : P.support.idxOf b = P.support.idxOf a + 1 := by
        unfold Nat.dist at hdist
        omega
      have haidx : P.support.idxOf a = i := by omega
      have hbidx : P.support.idxOf b = i + 1 := by omega
      constructor
      · calc
          a = P.getVert (P.support.idxOf a) :=
            (P.getVert_support_idxOf haP).symm
          _ = P.getVert i := by rw [haidx]
      · calc
          b = P.getVert (P.support.idxOf b) :=
            (P.getVert_support_idxOf hbP).symm
          _ = P.getVert (i + 1) := by rw [hbidx]
    · have haGet : P.getVert (P.support.idxOf a) = a :=
        P.getVert_support_idxOf haP
      have haIdxLe : P.support.idxOf a ≤ P.length :=
        support_idxOf_le_length P haP
      have hatt : P.support.idxOf a ∈
          offCorridorAttachmentIndices P (offCorridorComponentOf P b hbP) := by
        apply attachment_mem_of_offCorridor_adj P hbP haIdxLe
        simpa [haGet] using hab.symm
      have hbLeft : b ∈ corridorLeftRegion P i :=
        (mem_corridorLeftRegion_of_not_mem_support P i hbP).2
          ⟨P.support.idxOf a, hatt, hai⟩
      exact (hb hbLeft).elim
  · obtain ⟨j, hjatt, hji⟩ :=
      (mem_corridorLeftRegion_of_not_mem_support P i haP).1 ha
    by_cases hbP : b ∈ P.support
    · have hib : i < P.support.idxOf b := by
        by_contra hnot
        exact hb ((mem_corridorLeftRegion_of_mem_support P i hbP).2 (by omega))
      have hbIdxLe : P.support.idxOf b ≤ P.length :=
        support_idxOf_le_length P hbP
      have hbGet : P.getVert (P.support.idxOf b) = b :=
        P.getVert_support_idxOf hbP
      have hbatt : P.support.idxOf b ∈
          offCorridorAttachmentIndices P (offCorridorComponentOf P a haP) := by
        apply attachment_mem_of_offCorridor_adj P haP hbIdxLe
        simpa [hbGet] using hab
      exact (hno (offCorridorComponentOf P a haP)
        ⟨j, hjatt, P.support.idxOf b, hbatt, hji, by omega⟩).elim
    · have hcomp := offCorridorComponentOf_eq_of_adj P haP hbP hab
      have hbLeft : b ∈ corridorLeftRegion P i :=
        (mem_corridorLeftRegion_of_not_mem_support P i hbP).2
          ⟨j, by simpa [hcomp] using hjatt, hji⟩
      exact (hb hbLeft).elim

/-- A walk whose endpoints lie on opposite sides of a set uses an edge
crossing that set.  The crossing edge can be prescribed when every oriented
crossing has the same underlying edge. -/
theorem Walk.mem_edges_of_crossing_eq
    {G : SimpleGraph V} {a b : V} (W : G.Walk a b)
    (T : Set V) (e : Sym2 V) (ha : a ∈ T) (hb : b ∉ T)
    (hcross : ∀ {x y : V}, x ∈ T → y ∉ T → G.Adj x y → s(x, y) = e) :
    e ∈ W.edges := by
  induction W with
  | nil => exact (hb ha).elim
  | @cons a a' b haa' W ih =>
      by_cases ha' : a' ∈ T
      · rw [Walk.edges_cons]
        exact List.mem_cons_of_mem _ (ih ha' hb)
      · have hedge := hcross ha ha' haa'
        simpa [Walk.edges_cons, hedge]

/-- If no off-corridor component has attachments on both sides of a
corridor edge, that edge is a bridge. -/
theorem IsGeodesic.isBridge_of_forall_not_coversIndex
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v : V}
    {P : G.Walk u v} (hP : IsGeodesic P) {i : ℕ} (hi : i < P.length)
    (hno : ∀ C : OffCorridorComponent P,
      ¬offCorridorComponentCoversIndex P C i) :
    G.IsBridge s(P.getVert i, P.getVert (i + 1)) := by
  rw [isBridge_iff_adj_and_forall_walk_mem_edges]
  constructor
  · exact P.adj_getVert_succ hi
  · intro W
    let T := corridorLeftRegion P i
    have hstart : P.getVert i ∈ T :=
      hP.getVert_mem_corridorLeftRegion hi.le le_rfl
    have hend : P.getVert (i + 1) ∉ T :=
      hP.getVert_not_mem_corridorLeftRegion (by omega) (by omega)
    apply Erdos23GapGA.Walk.mem_edges_of_crossing_eq W T
      s(P.getVert i, P.getVert (i + 1)) hstart hend
    intro x y hx hy hxy
    obtain ⟨rfl, rfl⟩ := corridorLeftRegion_crossing_eq hP hno hx hy hxy
    rfl

/-- Every nonbridge corridor edge is covered by the attachment interval of
some canonical off-corridor component.

This is the exact ride-owner existence statement required by the paper
proof; it is stronger than choosing an owner only for edges also ridden by
`Q`. -/
theorem IsGeodesic.exists_offCorridorComponent_coversIndex_of_not_isBridge
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v : V}
    {P : G.Walk u v} (hP : IsGeodesic P) {i : ℕ} (hi : i < P.length)
    (hnonbridge : ¬G.IsBridge s(P.getVert i, P.getVert (i + 1))) :
    ∃ C : OffCorridorComponent P, offCorridorComponentCoversIndex P C i := by
  classical
  by_contra hnone
  have hno : ∀ C : OffCorridorComponent P,
      ¬offCorridorComponentCoversIndex P C i := by
    intro C hcover
    exact hnone ⟨C, hcover⟩
  exact hnonbridge (hP.isBridge_of_forall_not_coversIndex hi hno)

/-- Canonical choice of one covering component for each actually ridden
corridor edge.  No optimization of the choice is required by the packing
argument: every fiber remains a subset of its chosen component interval. -/
noncomputable def canonicalRiddenOwner
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z} (hP : IsGeodesic P)
    (hnonbridge : ∀ {a b : V}, s(a, b) ∈ P.edges →
      s(a, b) ∈ Q.edges → ¬G.IsBridge s(a, b)) :
    RiddenCorridorEdgeIndex P Q → OffCorridorComponent P := by
  classical
  intro i
  have hiData := (mem_riddenCorridorEdgeIndices P Q i.1).1 i.2
  have heP : s(P.getVert i.1, P.getVert (i.1 + 1)) ∈ P.edges :=
    hP.mem_edges_of_adj_of_mem_support (P.adj_getVert_succ hiData.1)
      (P.getVert_mem_support i.1) (P.getVert_mem_support (i.1 + 1))
  exact Classical.choose
    (hP.exists_offCorridorComponent_coversIndex_of_not_isBridge hiData.1
      (hnonbridge heP hiData.2))

/-- The chosen ridden-edge owner really covers its edge coordinate. -/
theorem canonicalRiddenOwner_covers
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z} (hP : IsGeodesic P)
    (hnonbridge : ∀ {a b : V}, s(a, b) ∈ P.edges →
      s(a, b) ∈ Q.edges → ¬G.IsBridge s(a, b))
    (i : RiddenCorridorEdgeIndex P Q) :
    offCorridorComponentCoversIndex P
      (canonicalRiddenOwner hP hnonbridge i) i.1 := by
  classical
  have hiData := (mem_riddenCorridorEdgeIndices P Q i.1).1 i.2
  have heP : s(P.getVert i.1, P.getVert (i.1 + 1)) ∈ P.edges :=
    hP.mem_edges_of_adj_of_mem_support (P.adj_getVert_succ hiData.1)
      (P.getVert_mem_support i.1) (P.getVert_mem_support (i.1 + 1))
  exact Classical.choose_spec
    (hP.exists_offCorridorComponent_coversIndex_of_not_isBridge hiData.1
      (hnonbridge heP hiData.2))

/-- The actual corridor-edge interval between the extreme attachments of a
component. -/
noncomputable def offCorridorComponentIntervalEdges
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (P : G.Walk u v) (C : OffCorridorComponent P) : Finset ℕ := by
  classical
  let A := offCorridorAttachmentIndices P C
  exact if hA : A.Nonempty then Finset.Ico (A.min' hA) (A.max' hA) else ∅

/-- The finite interval has exactly the previously defined component span. -/
theorem card_offCorridorComponentIntervalEdges
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (P : G.Walk u v) (C : OffCorridorComponent P) :
    (offCorridorComponentIntervalEdges P C).card =
      offCorridorComponentSpan P C := by
  classical
  let A := offCorridorAttachmentIndices P C
  by_cases hA : A.Nonempty
  · simp [offCorridorComponentIntervalEdges, offCorridorComponentSpan, A,
      hA, Nat.card_Ico]
  · simp [offCorridorComponentIntervalEdges, offCorridorComponentSpan, A, hA]

/-- A covered corridor coordinate belongs to the actual component interval. -/
theorem mem_offCorridorComponentIntervalEdges_of_coversIndex
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (P : G.Walk u v) (C : OffCorridorComponent P) {i : ℕ}
    (hcover : offCorridorComponentCoversIndex P C i) :
    i ∈ offCorridorComponentIntervalEdges P C := by
  classical
  obtain ⟨l, hl, h, hh, hli, hih⟩ := hcover
  let A := offCorridorAttachmentIndices P C
  have hA : A.Nonempty := ⟨l, hl⟩
  have hmin : A.min' hA ≤ l := A.min'_le l hl
  have hmax : h ≤ A.max' hA := A.le_max' h hh
  have hinterval : offCorridorComponentIntervalEdges P C =
      Finset.Ico (A.min' hA) (A.max' hA) := by
    simp [offCorridorComponentIntervalEdges, A, hA]
  rw [hinterval]
  exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩

/-- The whole edge interval between any two attachment coordinates is
contained in the component's extreme attachment interval. -/
theorem attachmentGapEdges_subset_componentInterval
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (P : G.Walk u v) (C : OffCorridorComponent P) {a b : ℕ}
    (ha : a ∈ offCorridorAttachmentIndices P C)
    (hb : b ∈ offCorridorAttachmentIndices P C) :
    Finset.Ico (min a b) (max a b) ⊆
      offCorridorComponentIntervalEdges P C := by
  classical
  let A := offCorridorAttachmentIndices P C
  have hA : A.Nonempty := ⟨a, ha⟩
  have hminA : A.min' hA ≤ min a b := by
    exact le_min (A.min'_le a ha) (A.min'_le b hb)
  have hmaxA : max a b ≤ A.max' hA := by
    exact max_le (A.le_max' a ha) (A.le_max' b hb)
  intro j hj
  have hj' := Finset.mem_Ico.mp hj
  have hinterval : offCorridorComponentIntervalEdges P C =
      Finset.Ico (A.min' hA) (A.max' hA) := by
    simp [offCorridorComponentIntervalEdges, A, hA]
  rw [hinterval]
  exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩

/-! ## Ordered common visits -/

/-- The filtered common-visit list embeds, in order, into the support list
of `Q`. -/
noncomputable def corridorVisitEmbedding
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    (P : G.Walk w x₀) (Q : G.Walk y z) :
    Fin (corridorVisitVertices P Q).length ↪o Fin Q.support.length := by
  classical
  exact Classical.choose
    ((List.sublist_iff_exists_fin_orderEmbedding_get_eq).1 (by
      simpa [corridorVisitVertices] using
        (List.filter_sublist :
          List.Sublist (Q.support.filter fun x => x ∈ P.support) Q.support)))

theorem corridorVisitEmbedding_get
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    (P : G.Walk w x₀) (Q : G.Walk y z)
    (k : Fin (corridorVisitVertices P Q).length) :
    (corridorVisitVertices P Q).get k =
      Q.support.get (corridorVisitEmbedding P Q k) := by
  classical
  exact Classical.choose_spec
    ((List.sublist_iff_exists_fin_orderEmbedding_get_eq).1 (by
      simpa [corridorVisitVertices] using
        (List.filter_sublist :
          List.Sublist (Q.support.filter fun x => x ∈ P.support) Q.support))) k

/-- Every filtered common visit belongs to both path supports. -/
theorem corridorVisitVertex_mem_supports
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    (P : G.Walk w x₀) (Q : G.Walk y z)
    (k : Fin (corridorVisitVertices P Q).length) :
    (corridorVisitVertices P Q).get k ∈ P.support ∧
      (corridorVisitVertices P Q).get k ∈ Q.support := by
  have hk := List.get_mem (corridorVisitVertices P Q) k
  have hk' : (corridorVisitVertices P Q).get k ∈ Q.support ∧
      (corridorVisitVertices P Q).get k ∈ P.support := by
    change (corridorVisitVertices P Q).get k ∈
      Q.support.filter (fun x => x ∈ P.support) at hk
    simpa using (List.mem_filter.mp hk)
  exact hk'.symm

/-- Corridor coordinate of the `k`th common visit in `Q` order. -/
def corridorVisitIndexAt
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    (P : G.Walk w x₀) (Q : G.Walk y z)
    (k : Fin (corridorVisitVertices P Q).length) : ℕ :=
  P.support.idxOf ((corridorVisitVertices P Q).get k)

/-- The `Q`-coordinate of a filtered common visit is exactly the value of
the order embedding. -/
theorem IsGeodesic.support_idxOf_corridorVisitVertex
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    (P : G.Walk w x₀) {Q : G.Walk y z} (hQ : IsGeodesic Q)
    (k : Fin (corridorVisitVertices P Q).length) :
    Q.support.idxOf ((corridorVisitVertices P Q).get k) =
      corridorVisitEmbedding P Q k := by
  rw [corridorVisitEmbedding_get]
  exact List.get_idxOf hQ.isPath.support_nodup _

/-- Every `Q`-support position whose vertex also lies on `P` is in the
ordered common-visit embedding. -/
theorem IsGeodesic.exists_corridorVisitEmbedding_eq_of_mem_P
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    (P : G.Walk w x₀) {Q : G.Walk y z} (hQ : IsGeodesic Q)
    (k : Fin Q.support.length) (hkP : Q.support.get k ∈ P.support) :
    ∃ j : Fin (corridorVisitVertices P Q).length,
      corridorVisitEmbedding P Q j = k := by
  let x := Q.support.get k
  have hxQ : x ∈ Q.support := List.get_mem Q.support k
  have hxVisits : x ∈ corridorVisitVertices P Q := by
    change x ∈ Q.support.filter (fun y => y ∈ P.support)
    exact List.mem_filter.mpr ⟨hxQ, by simpa using hkP⟩
  let j : Fin (corridorVisitVertices P Q).length :=
    ⟨(corridorVisitVertices P Q).idxOf x,
      List.idxOf_lt_length_of_mem hxVisits⟩
  have hjget : (corridorVisitVertices P Q).get j = x := by
    simpa [j] using List.getElem_idxOf
      (List.idxOf_lt_length_of_mem hxVisits)
  refine ⟨j, ?_⟩
  apply (List.nodup_iff_injective_get.mp hQ.isPath.support_nodup)
  rw [← corridorVisitEmbedding_get P Q j, hjget]

/-- Every middle common visit lies between the outer two in corridor
coordinates. -/
theorem corridorVisitIndexAt_between
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    {i j k : Fin (corridorVisitVertices P Q).length}
    (hij : i < j) (hjk : j < k) :
    (corridorVisitIndexAt P Q i ≤ corridorVisitIndexAt P Q j ∧
        corridorVisitIndexAt P Q j ≤ corridorVisitIndexAt P Q k) ∨
      (corridorVisitIndexAt P Q k ≤ corridorVisitIndexAt P Q j ∧
        corridorVisitIndexAt P Q j ≤ corridorVisitIndexAt P Q i) := by
  let xi := (corridorVisitVertices P Q).get i
  let xj := (corridorVisitVertices P Q).get j
  let xk := (corridorVisitVertices P Q).get k
  have hiMem := corridorVisitVertex_mem_supports P Q i
  have hjMem := corridorVisitVertex_mem_supports P Q j
  have hkMem := corridorVisitVertex_mem_supports P Q k
  apply corridor_index_between_of_Q_order hP hQ
    hiMem.1 hiMem.2 hjMem.1 hjMem.2 hkMem.1 hkMem.2
  · rw [hQ.support_idxOf_corridorVisitVertex P,
      hQ.support_idxOf_corridorVisitVertex P]
    exact (corridorVisitEmbedding P Q).monotone hij.le
  · rw [hQ.support_idxOf_corridorVisitVertex P,
      hQ.support_idxOf_corridorVisitVertex P]
    exact (corridorVisitEmbedding P Q).monotone hjk.le

/-- A finite injective sequence in which every middle term lies between the
outer two is globally strictly increasing or globally strictly decreasing. -/
theorem strictMono_or_strictAnti_of_between
    {n : ℕ} (f : Fin n → ℕ) (hn : 2 ≤ n) (hinj : Function.Injective f)
    (hbetween : ∀ {i j k : Fin n}, i < j → j < k →
      (f i ≤ f j ∧ f j ≤ f k) ∨ (f k ≤ f j ∧ f j ≤ f i)) :
    StrictMono f ∨ StrictAnti f := by
  let z : Fin n := ⟨0, by omega⟩
  let o : Fin n := ⟨1, by omega⟩
  have hzo : z < o := by simp [z, o]
  have hne : f z ≠ f o := by
    intro h
    exact (Fin.ne_of_lt hzo) (hinj h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · left
    intro i j hij
    by_cases hiz : i = z
    · subst i
      by_cases hjo : j = o
      · simpa [hjo] using hlt
      · have hoj : o < j := by
          apply Fin.mk_lt_mk.mpr
          have hjpos : 0 < j.1 := by
            simpa [z] using hij
          have hjne : j.1 ≠ 1 := by
            intro h
            apply hjo
            apply Fin.ext
            simpa [o] using h
          omega
        rcases hbetween hzo hoj with hforward | hreverse
        · omega
        · omega
    · have hzi : z < i := by
        apply Fin.mk_lt_mk.mpr
        have : i.1 ≠ 0 := by
          intro h
          apply hiz
          apply Fin.ext
          simpa [z] using h
        omega

      have hfzi : f z < f i := by
        by_cases hio : i = o
        · simpa [hio] using hlt
        · have hoi : o < i := by
            apply Fin.mk_lt_mk.mpr
            have hi0 : i.1 ≠ 0 := by
              intro h
              apply hiz
              apply Fin.ext
              simpa [z] using h
            have hi1 : i.1 ≠ 1 := by
              intro h
              apply hio
              apply Fin.ext
              simpa [o] using h
            omega
          rcases hbetween hzo hoi with hforward | hreverse
          · have hnezi : f z ≠ f i := by
              intro h
              exact (Fin.ne_of_lt hzi) (hinj h)
            omega
          · omega
      rcases hbetween hzi hij with hforward | hreverse
      · have hneij : f i ≠ f j := by
          intro h
          exact (Fin.ne_of_lt hij) (hinj h)
        omega
      · omega
  · right
    intro i j hij
    by_cases hiz : i = z
    · subst i
      by_cases hjo : j = o
      · simpa [hjo] using hgt
      · have hoj : o < j := by
          apply Fin.mk_lt_mk.mpr
          have hjpos : 0 < j.1 := by
            simpa [z] using hij
          have hjne : j.1 ≠ 1 := by
            intro h
            apply hjo
            apply Fin.ext
            simpa [o] using h
          omega
        rcases hbetween hzo hoj with hforward | hreverse
        · omega
        · omega
    · have hzi : z < i := by
        apply Fin.mk_lt_mk.mpr
        have : i.1 ≠ 0 := by
          intro h
          apply hiz
          apply Fin.ext
          simpa [z] using h
        omega
      have hfiz : f i < f z := by
        by_cases hio : i = o
        · simpa [hio] using hgt
        · have hoi : o < i := by
            apply Fin.mk_lt_mk.mpr
            have hi0 : i.1 ≠ 0 := by
              intro h
              apply hiz
              apply Fin.ext
              simpa [z] using h
            have hi1 : i.1 ≠ 1 := by
              intro h
              apply hio
              apply Fin.ext
              simpa [o] using h
            omega
          rcases hbetween hzo hoi with hforward | hreverse
          · omega
          · have hnezi : f z ≠ f i := by
              intro h
              exact (Fin.ne_of_lt hzi) (hinj h)
            omega
      rcases hbetween hzi hij with hforward | hreverse
      · omega
      · have hneij : f i ≠ f j := by
          intro h
          exact (Fin.ne_of_lt hij) (hinj h)
        omega

/-- Distinct common visits have distinct corridor coordinates. -/
theorem IsGeodesic.corridorVisitIndexAt_injective
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hQ : IsGeodesic Q) :
    Function.Injective (corridorVisitIndexAt P Q) := by
  intro i j hij
  apply (List.nodup_iff_injective_get.mp
    hQ.corridorVisitVertices_nodup)
  have hiMem := corridorVisitVertex_mem_supports P Q i
  have hjMem := corridorVisitVertex_mem_supports P Q j
  calc
    (corridorVisitVertices P Q).get i =
        P.getVert (corridorVisitIndexAt P Q i) :=
      (P.getVert_support_idxOf hiMem.1).symm
    _ = P.getVert (corridorVisitIndexAt P Q j) := by rw [hij]
    _ = (corridorVisitVertices P Q).get j :=
      P.getVert_support_idxOf hjMem.1

/-- Once there are at least two common vertices, their corridor coordinates
in `Q` order are globally strictly monotone, in one of the two orientations.
This closes the ordered-visit node of the paper proof without choosing an
orientation for `Q`. -/
theorem IsGeodesic.strictMono_or_strictAnti_corridorVisitIndexAt
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (htwo : 2 ≤ (commonVertices P Q).card) :
    StrictMono (corridorVisitIndexAt P Q) ∨
      StrictAnti (corridorVisitIndexAt P Q) := by
  have hlen : 2 ≤ (corridorVisitVertices P Q).length := by
    rw [hQ.length_corridorVisitVertices_eq_card_commonVertices]
    exact htwo
  apply strictMono_or_strictAnti_of_between
    (corridorVisitIndexAt P Q) hlen
    (hQ.corridorVisitIndexAt_injective)
  intro i j k hij hjk
  exact corridorVisitIndexAt_between hP hQ hij hjk

/-! ## Consecutive common-visit transitions -/

/-- An index for a consecutive pair in the common-visit list. -/
abbrev CorridorTransition [DecidableEq V]
    {G : SimpleGraph V} {w x₀ y z : V}
    (P : G.Walk w x₀) (Q : G.Walk y z) :=
  Fin ((corridorVisitVertices P Q).length - 1)

def corridorTransitionStart
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    (P : G.Walk w x₀) (Q : G.Walk y z)
    (t : CorridorTransition P Q) :
    Fin (corridorVisitVertices P Q).length :=
  ⟨t.1, by omega⟩

def corridorTransitionEnd
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    (P : G.Walk w x₀) (Q : G.Walk y z)
    (t : CorridorTransition P Q) :
    Fin (corridorVisitVertices P Q).length :=
  ⟨t.1 + 1, by omega⟩

theorem corridorTransitionStart_lt_end
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    (P : G.Walk w x₀) (Q : G.Walk y z)
    (t : CorridorTransition P Q) :
    corridorTransitionStart P Q t < corridorTransitionEnd P Q t := by
  simp [corridorTransitionStart, corridorTransitionEnd]

/-- The unordered corridor gap of one consecutive common-visit transition. -/
def corridorTransitionGap
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    (P : G.Walk w x₀) (Q : G.Walk y z)
    (t : CorridorTransition P Q) : ℕ :=
  Nat.dist
    (corridorVisitIndexAt P Q (corridorTransitionStart P Q t))
    (corridorVisitIndexAt P Q (corridorTransitionEnd P Q t))

/-- The corridor edges spanned by one transition. -/
def corridorTransitionGapEdges
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    (P : G.Walk w x₀) (Q : G.Walk y z)
    (t : CorridorTransition P Q) : Finset ℕ :=
  Finset.Ico
    (min (corridorVisitIndexAt P Q (corridorTransitionStart P Q t))
      (corridorVisitIndexAt P Q (corridorTransitionEnd P Q t)))
    (max (corridorVisitIndexAt P Q (corridorTransitionStart P Q t))
      (corridorVisitIndexAt P Q (corridorTransitionEnd P Q t)))

theorem card_corridorTransitionGapEdges
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    (P : G.Walk w x₀) (Q : G.Walk y z)
    (t : CorridorTransition P Q) :
    (corridorTransitionGapEdges P Q t).card =
      corridorTransitionGap P Q t := by
  simp [corridorTransitionGapEdges, corridorTransitionGap,
    Nat.card_Ico, Nat.dist_eq_max_sub_min]

/-- Consecutive visits in the filtered list occur in strict `Q`-support
order. -/
theorem corridorTransition_embedding_lt
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    (P : G.Walk w x₀) (Q : G.Walk y z)
    (t : CorridorTransition P Q) :
    corridorVisitEmbedding P Q (corridorTransitionStart P Q t) <
      corridorVisitEmbedding P Q (corridorTransitionEnd P Q t) :=
  (corridorVisitEmbedding P Q).strictMono
    (corridorTransitionStart_lt_end P Q t)

/-- A support position strictly between two consecutive common visits is
off the corridor `P`. -/
theorem IsGeodesic.corridorTransition_interior_not_mem_support
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    (P : G.Walk w x₀) {Q : G.Walk y z} (hQ : IsGeodesic Q)
    (t : CorridorTransition P Q) (k : Fin Q.support.length)
    (hleft : corridorVisitEmbedding P Q
        (corridorTransitionStart P Q t) < k)
    (hright : k < corridorVisitEmbedding P Q
        (corridorTransitionEnd P Q t)) :
    Q.support.get k ∉ P.support := by
  intro hkP
  obtain ⟨j, hj⟩ := hQ.exists_corridorVisitEmbedding_eq_of_mem_P P k hkP
  have hsj : corridorTransitionStart P Q t < j := by
    apply (corridorVisitEmbedding P Q).lt_iff_lt.mp
    rw [hj]
    exact hleft
  have hje : j < corridorTransitionEnd P Q t := by
    apply (corridorVisitEmbedding P Q).lt_iff_lt.mp
    rw [hj]
    exact hright
  have hsj' := Fin.mk_lt_mk.mp hsj
  have hje' := Fin.mk_lt_mk.mp hje
  simp [corridorTransitionStart, corridorTransitionEnd] at hsj' hje'
  omega

/-- Consecutive positions in a walk support are adjacent in the graph. -/
theorem Walk.adj_support_get_succ
    {G : SimpleGraph V} {u v : V} (W : G.Walk u v)
    (k : ℕ) (hk : k + 1 < W.support.length) :
    G.Adj (W.support.get ⟨k, by omega⟩)
      (W.support.get ⟨k + 1, hk⟩) := by
  have hklen : k < W.length := by
    rw [Walk.length_support] at hk
    omega
  simpa [W.getVert_eq_support_getElem hklen.le,
    W.getVert_eq_support_getElem (by omega : k + 1 ≤ W.length)] using
      W.adj_getVert_succ hklen

/-- All support vertices strictly inside one common-visit transition lie in
the same off-corridor component. -/
theorem IsGeodesic.offCorridorComponentOf_support_get_eq_of_transition_interior
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    (P : G.Walk w x₀) {Q : G.Walk y z} (hQ : IsGeodesic Q)
    (t : CorridorTransition P Q) {k l : ℕ}
    (hklen : k < Q.support.length) (hllen : l < Q.support.length)
    (hleft : (corridorVisitEmbedding P Q
      (corridorTransitionStart P Q t) : ℕ) < k)
    (hkl : k ≤ l)
    (hright : l < corridorVisitEmbedding P Q
      (corridorTransitionEnd P Q t))
    (hkoff : Q.support.get ⟨k, hklen⟩ ∉ P.support)
    (hloff : Q.support.get ⟨l, hllen⟩ ∉ P.support) :
    offCorridorComponentOf P (Q.support.get ⟨k, hklen⟩) hkoff =
      offCorridorComponentOf P (Q.support.get ⟨l, hllen⟩) hloff := by
  let first :=
    offCorridorComponentOf P (Q.support.get ⟨k, hklen⟩) hkoff
  let Pred : (n : ℕ) → k ≤ n → Prop := fun n _ =>
    ∀ (hnlen : n < Q.support.length)
      (hnright : n < corridorVisitEmbedding P Q
        (corridorTransitionEnd P Q t))
      (hnoff : Q.support.get ⟨n, hnlen⟩ ∉ P.support),
      first = offCorridorComponentOf P
        (Q.support.get ⟨n, hnlen⟩) hnoff
  refine Nat.le_induction (P := Pred) ?_ ?_ l hkl hllen hright hloff
  · intro _hnlen _hnright _hnoff
    rfl
  · intro n hkn ihn hsuccLen hsuccRight hsuccOff
    have hnlen : n < Q.support.length := by omega
    have hnright : n < corridorVisitEmbedding P Q
        (corridorTransitionEnd P Q t) := by omega
    let nf : Fin Q.support.length := ⟨n, hnlen⟩
    have hleftFin : corridorVisitEmbedding P Q
        (corridorTransitionStart P Q t) < nf := by
      apply Fin.mk_lt_mk.mpr
      exact lt_of_lt_of_le hleft hkn
    have hrightFin : nf < corridorVisitEmbedding P Q
        (corridorTransitionEnd P Q t) := by
      exact hnright
    have hnoff : Q.support.get nf ∉ P.support :=
      hQ.corridorTransition_interior_not_mem_support P t nf
        hleftFin hrightFin
    calc
      first = offCorridorComponentOf P (Q.support.get nf) hnoff :=
        ihn hnlen hnright hnoff
      _ = offCorridorComponentOf P
          (Q.support.get ⟨n + 1, hsuccLen⟩) hsuccOff := by
        apply offCorridorComponentOf_eq_of_adj
        exact Erdos23GapGA.Walk.adj_support_get_succ Q n hsuccLen

/-- A nontrivial consecutive transition has a genuine off-corridor
component attached at both endpoint coordinates, and its whole corridor gap
interval lies in that component's attachment interval. -/
theorem IsGeodesic.exists_excursionComponent_for_transition
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (t : CorridorTransition P Q) (hgap : 1 < corridorTransitionGap P Q t) :
    ∃ C : OffCorridorComponent P,
      corridorVisitIndexAt P Q (corridorTransitionStart P Q t) ∈
          offCorridorAttachmentIndices P C ∧
        corridorVisitIndexAt P Q (corridorTransitionEnd P Q t) ∈
          offCorridorAttachmentIndices P C ∧
        corridorTransitionGapEdges P Q t ⊆
          offCorridorComponentIntervalEdges P C ∧
        ∀ k : Fin Q.support.length,
          corridorVisitEmbedding P Q (corridorTransitionStart P Q t) < k →
          k < corridorVisitEmbedding P Q (corridorTransitionEnd P Q t) →
          Q.support.get k ∈ offCorridorComponentFinset C := by
  classical
  let s := corridorTransitionStart P Q t
  let e := corridorTransitionEnd P Q t
  let qa : ℕ := corridorVisitEmbedding P Q s
  let qb : ℕ := corridorVisitEmbedding P Q e
  have hsMem := corridorVisitVertex_mem_supports P Q s
  have heMem := corridorVisitVertex_mem_supports P Q e
  have hdist := common_index_dist_eq hP hQ
    hsMem.1 hsMem.2 heMem.1 heMem.2
  rw [hQ.support_idxOf_corridorVisitVertex P,
    hQ.support_idxOf_corridorVisitVertex P] at hdist
  have hqale : qa ≤ qb := by
    exact (corridorVisitEmbedding P Q).monotone
      (corridorTransitionStart_lt_end P Q t).le
  have hgapEq : corridorTransitionGap P Q t = qb - qa := by
    rw [corridorTransitionGap]
    change Nat.dist (P.support.idxOf ((corridorVisitVertices P Q).get s))
      (P.support.idxOf ((corridorVisitVertices P Q).get e)) = qb - qa
    rw [hdist, Nat.dist_eq_sub_of_le hqale]
  have hqa1qb : qa + 1 < qb := by omega
  have hqbLen : qb < Q.support.length := by
    exact (corridorVisitEmbedding P Q e).isLt
  have hqa1Len : qa + 1 < Q.support.length := by omega
  let first : Fin Q.support.length := ⟨qa + 1, hqa1Len⟩
  have hfirstLeft : corridorVisitEmbedding P Q s < first := by
    apply Fin.mk_lt_mk.mpr
    simp [qa, first]
  have hfirstRight : first < corridorVisitEmbedding P Q e := by
    apply Fin.mk_lt_mk.mpr
    simpa [qb, first] using hqa1qb
  have hfirstOff : Q.support.get first ∉ P.support :=
    hQ.corridorTransition_interior_not_mem_support P t first
      (by simpa [s] using hfirstLeft) (by simpa [e] using hfirstRight)
  let C : OffCorridorComponent P :=
    offCorridorComponentOf P (Q.support.get first) hfirstOff
  have hstartMem := corridorVisitVertex_mem_supports P Q s
  have hstartIdxLe : corridorVisitIndexAt P Q s ≤ P.length :=
    support_idxOf_le_length P hstartMem.1
  have hstartAdjQ : G.Adj
      (Q.support.get first)
      (Q.support.get (corridorVisitEmbedding P Q s)) := by
    have hadj := Erdos23GapGA.Walk.adj_support_get_succ Q qa hqa1Len
    simpa [qa, first] using hadj.symm
  have hstartVisitEq : Q.support.get (corridorVisitEmbedding P Q s) =
      P.getVert (corridorVisitIndexAt P Q s) := by
    calc
      Q.support.get (corridorVisitEmbedding P Q s) =
          (corridorVisitVertices P Q).get s :=
        (corridorVisitEmbedding_get P Q s).symm
      _ = P.getVert (corridorVisitIndexAt P Q s) :=
        (P.getVert_support_idxOf hstartMem.1).symm
  have hstartAdj : G.Adj (Q.support.get first)
      (P.getVert (corridorVisitIndexAt P Q s)) := by
    rw [hstartVisitEq] at hstartAdjQ
    exact hstartAdjQ
  have hstartAtt : corridorVisitIndexAt P Q s ∈
      offCorridorAttachmentIndices P C := by
    exact attachment_mem_of_offCorridor_adj P hfirstOff hstartIdxLe hstartAdj
  let lastNat := qb - 1
  have hlastEq : lastNat + 1 = qb := by
    dsimp [lastNat]
    omega
  have hlastLen : lastNat < Q.support.length := by omega
  let last : Fin Q.support.length := ⟨lastNat, hlastLen⟩
  have hlastLeft : corridorVisitEmbedding P Q s < last := by
    apply Fin.mk_lt_mk.mpr
    dsimp [last, lastNat, qa, qb]
    omega
  have hlastRight : last < corridorVisitEmbedding P Q e := by
    apply Fin.mk_lt_mk.mpr
    dsimp [last, lastNat, qb]
    omega
  have hlastOff : Q.support.get last ∉ P.support :=
    hQ.corridorTransition_interior_not_mem_support P t last
      (by simpa [s] using hlastLeft) (by simpa [e] using hlastRight)
  have hfirstLast : (first : ℕ) ≤ last := by
    dsimp [first, last, lastNat]
    omega
  have hcomp : C = offCorridorComponentOf P (Q.support.get last) hlastOff := by
    dsimp [C]
    apply hQ.offCorridorComponentOf_support_get_eq_of_transition_interior P t
      hqa1Len hlastLen
    · dsimp [first, qa]
      omega
    · exact hfirstLast
    · dsimp [last, lastNat, qb]
      omega
  have hendMem := corridorVisitVertex_mem_supports P Q e
  have hendIdxLe : corridorVisitIndexAt P Q e ≤ P.length :=
    support_idxOf_le_length P hendMem.1
  have hendAdjQ : G.Adj (Q.support.get last)
      (Q.support.get (corridorVisitEmbedding P Q e)) := by
    have hadj := Erdos23GapGA.Walk.adj_support_get_succ Q lastNat (by
      rw [hlastEq]
      exact hqbLen)
    have hlastSucc : lastNat + 1 =
        (corridorVisitEmbedding P Q e : ℕ) := by
      simpa [qb] using hlastEq
    simpa [last, hlastSucc] using hadj
  have hendVisitEq : Q.support.get (corridorVisitEmbedding P Q e) =
      P.getVert (corridorVisitIndexAt P Q e) := by
    calc
      Q.support.get (corridorVisitEmbedding P Q e) =
          (corridorVisitVertices P Q).get e :=
        (corridorVisitEmbedding_get P Q e).symm
      _ = P.getVert (corridorVisitIndexAt P Q e) :=
        (P.getVert_support_idxOf hendMem.1).symm
  have hendAdj : G.Adj (Q.support.get last)
      (P.getVert (corridorVisitIndexAt P Q e)) := by
    rw [hendVisitEq] at hendAdjQ
    exact hendAdjQ
  have hendAttLast : corridorVisitIndexAt P Q e ∈
      offCorridorAttachmentIndices P
        (offCorridorComponentOf P (Q.support.get last) hlastOff) :=
    attachment_mem_of_offCorridor_adj P hlastOff hendIdxLe hendAdj
  have hendAtt : corridorVisitIndexAt P Q e ∈
      offCorridorAttachmentIndices P C := by
    simpa [hcomp] using hendAttLast
  refine ⟨C, hstartAtt, hendAtt, ?_, ?_⟩
  · simpa [corridorTransitionGapEdges, s, e] using
      attachmentGapEdges_subset_componentInterval P C hstartAtt hendAtt
  · intro k hkLeft hkRight
    have hkOff : Q.support.get k ∉ P.support :=
      hQ.corridorTransition_interior_not_mem_support P t k hkLeft hkRight
    have hfirstK : (first : ℕ) ≤ k := by
      dsimp [first, qa]
      exact Nat.succ_le_iff.mpr (Fin.mk_lt_mk.mp hkLeft)
    have hcompK : C = offCorridorComponentOf P (Q.support.get k) hkOff := by
      dsimp [C]
      apply hQ.offCorridorComponentOf_support_get_eq_of_transition_interior P t
        hqa1Len k.isLt
      · dsimp [first, qa]
        omega
      · exact hfirstK
      · exact Fin.mk_lt_mk.mp hkRight
    have hmem := mem_offCorridorComponentOf P hkOff
    simpa [hcompK] using hmem

/-- The corridor gap equals the number of `Q` edges between the two visits. -/
theorem corridorTransitionGap_eq_Q_index_sub
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (t : CorridorTransition P Q) :
    corridorTransitionGap P Q t =
      (corridorVisitEmbedding P Q (corridorTransitionEnd P Q t) : ℕ) -
        corridorVisitEmbedding P Q (corridorTransitionStart P Q t) := by
  let a := corridorTransitionStart P Q t
  let b := corridorTransitionEnd P Q t
  have haMem := corridorVisitVertex_mem_supports P Q a
  have hbMem := corridorVisitVertex_mem_supports P Q b
  have hdist := common_index_dist_eq hP hQ
    haMem.1 haMem.2 hbMem.1 hbMem.2
  rw [hQ.support_idxOf_corridorVisitVertex P,
    hQ.support_idxOf_corridorVisitVertex P] at hdist
  have hab : (corridorVisitEmbedding P Q a : ℕ) ≤
      corridorVisitEmbedding P Q b :=
    (corridorVisitEmbedding P Q).monotone
      (corridorTransitionStart_lt_end P Q t).le
  have hdist' : corridorTransitionGap P Q t =
      Nat.dist (corridorVisitEmbedding P Q a)
        (corridorVisitEmbedding P Q b) := by
    simpa [corridorTransitionGap, corridorVisitIndexAt, a, b] using hdist
  rw [hdist', Nat.dist_eq_sub_of_le hab]

/-- Every consecutive common-visit transition has a nonempty corridor gap. -/
theorem corridorTransitionGap_pos
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (t : CorridorTransition P Q) :
    0 < corridorTransitionGap P Q t := by
  rw [corridorTransitionGap_eq_Q_index_sub hP hQ]
  have := corridorTransition_embedding_lt P Q t
  exact Nat.sub_pos_of_lt this

/-- A unit-gap transition is exactly one actually ridden corridor edge. -/
theorem IsGeodesic.exists_riddenIndex_of_transitionGap_eq_one
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (t : CorridorTransition P Q)
    (hgap : corridorTransitionGap P Q t = 1) :
    ∃ i : RiddenCorridorEdgeIndex P Q,
      i.1 = min
        (corridorVisitIndexAt P Q (corridorTransitionStart P Q t))
        (corridorVisitIndexAt P Q (corridorTransitionEnd P Q t)) ∧
      corridorTransitionGapEdges P Q t = {i.1} := by
  classical
  let s := corridorTransitionStart P Q t
  let e := corridorTransitionEnd P Q t
  let a := corridorVisitIndexAt P Q s
  let b := corridorVisitIndexAt P Q e
  let qa : ℕ := corridorVisitEmbedding P Q s
  let qb : ℕ := corridorVisitEmbedding P Q e
  have hqsub := corridorTransitionGap_eq_Q_index_sub hP hQ t
  have hqLt : qa < qb := by
    exact corridorTransition_embedding_lt P Q t
  have hqb : qb = qa + 1 := by
    have hqsub' : 1 = qb - qa := by
      calc
        1 = corridorTransitionGap P Q t := hgap.symm
        _ = qb - qa := by simpa [qa, qb, s, e] using hqsub
    omega
  have hqbLen : qb < Q.support.length :=
    (corridorVisitEmbedding P Q e).isLt
  have hqaLen : qa < Q.support.length := by omega
  have hadjQ : G.Adj (Q.support.get ⟨qa, hqaLen⟩)
      (Q.support.get ⟨qb, hqbLen⟩) := by
    have hadj := Erdos23GapGA.Walk.adj_support_get_succ Q qa (by omega)
    simpa [hqb] using hadj
  have heQ : s(Q.support.get ⟨qa, hqaLen⟩,
      Q.support.get ⟨qb, hqbLen⟩) ∈ Q.edges :=
    hQ.mem_edges_of_adj_of_mem_support hadjQ
      (List.get_mem Q.support ⟨qa, hqaLen⟩)
      (List.get_mem Q.support ⟨qb, hqbLen⟩)
  have hsMem := corridorVisitVertex_mem_supports P Q s
  have heMem := corridorVisitVertex_mem_supports P Q e
  have hstartEq : Q.support.get ⟨qa, hqaLen⟩ = P.getVert a := by
    calc
      Q.support.get ⟨qa, hqaLen⟩ =
          (corridorVisitVertices P Q).get s := by
        simpa [qa] using (corridorVisitEmbedding_get P Q s).symm
      _ = P.getVert a := (P.getVert_support_idxOf hsMem.1).symm
  have hendEq : Q.support.get ⟨qb, hqbLen⟩ = P.getVert b := by
    calc
      Q.support.get ⟨qb, hqbLen⟩ =
          (corridorVisitVertices P Q).get e := by
        simpa [qb] using (corridorVisitEmbedding_get P Q e).symm
      _ = P.getVert b := (P.getVert_support_idxOf heMem.1).symm
  rw [hstartEq, hendEq] at heQ
  have hpdist : Nat.dist a b = 1 := by
    simpa [corridorTransitionGap, a, b, s, e] using hgap
  have hab : b = a + 1 ∨ a = b + 1 := by
    unfold Nat.dist at hpdist
    omega
  rcases hab with hab | hba
  · have haLen : a < P.length := by
      have hbLe : b ≤ P.length := by
        exact support_idxOf_le_length P heMem.1
      omega
    let i : RiddenCorridorEdgeIndex P Q :=
      ⟨a, (mem_riddenCorridorEdgeIndices P Q a).2
        ⟨haLen, by simpa [hab] using heQ⟩⟩
    refine ⟨i, ?_, ?_⟩
    · change a = min a b
      omega
    · change Finset.Ico (min a b) (max a b) = {a}
      simp [hab]
  · have hbLen : b < P.length := by
      have haLe : a ≤ P.length := by
        exact support_idxOf_le_length P hsMem.1
      omega
    let i : RiddenCorridorEdgeIndex P Q :=
      ⟨b, (mem_riddenCorridorEdgeIndices P Q b).2
        ⟨hbLen, by simpa [hba, Sym2.eq_swap] using heQ⟩⟩
    refine ⟨i, ?_, ?_⟩
    · change b = min a b
      omega
    · change Finset.Ico (min a b) (max a b) = {b}
      simp [hba]

/-- If two values of a finite order embedding are consecutive, then their
source indices are consecutive as well. -/
theorem Fin.val_eq_add_one_of_orderEmbedding_image_eq_add_one
    {n m : ℕ} (f : Fin n ↪o Fin m) {i j : Fin n} (hij : i < j)
    (himage : (f j : ℕ) = (f i : ℕ) + 1) :
    (j : ℕ) = (i : ℕ) + 1 := by
  by_contra hne
  have hgap : (i : ℕ) + 1 < j := by omega
  let k : Fin n := ⟨(i : ℕ) + 1, by omega⟩
  have hik : i < k := by
    apply Fin.mk_lt_mk.mpr
    simp [k]
  have hkj : k < j := by
    apply Fin.mk_lt_mk.mpr
    exact hgap
  have hfik := f.strictMono hik
  have hfkj := f.strictMono hkj
  omega

/-- Conversely, every actually ridden corridor edge is the unit gap of a
unique-position consecutive common-visit transition.  This supplies the
surjectivity half needed for exact ride/excursion counting. -/
theorem IsGeodesic.exists_transition_of_riddenIndex
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (ri : RiddenCorridorEdgeIndex P Q) :
    ∃ t : CorridorTransition P Q,
      corridorTransitionGap P Q t = 1 ∧
        corridorTransitionGapEdges P Q t = {ri.1} := by
  classical
  let i := ri.1
  have hiData := (mem_riddenCorridorEdgeIndices P Q i).1 ri.2
  let A := P.getVert i
  let B := P.getVert (i + 1)
  have hAq : A ∈ Q.support := Q.fst_mem_support_of_mem_edges hiData.2
  have hBq : B ∈ Q.support := Q.snd_mem_support_of_mem_edges hiData.2
  have hAp : A ∈ P.support := P.getVert_mem_support i
  have hBp : B ∈ P.support := P.getVert_mem_support (i + 1)
  let qa : Fin Q.support.length :=
    ⟨Q.support.idxOf A, List.idxOf_lt_length_of_mem hAq⟩
  let qb : Fin Q.support.length :=
    ⟨Q.support.idxOf B, List.idxOf_lt_length_of_mem hBq⟩
  have hgetA : Q.support.get qa = A := by
    simpa [qa] using List.getElem_idxOf
      (List.idxOf_lt_length_of_mem hAq)
  have hgetB : Q.support.get qb = B := by
    simpa [qb] using List.getElem_idxOf
      (List.idxOf_lt_length_of_mem hBq)
  have hqaP : Q.support.get qa ∈ P.support := by
    rw [hgetA]
    exact hAp
  have hqbP : Q.support.get qb ∈ P.support := by
    rw [hgetB]
    exact hBp
  obtain ⟨ja, hja⟩ :=
    hQ.exists_corridorVisitEmbedding_eq_of_mem_P P qa hqaP
  obtain ⟨jb, hjb⟩ :=
    hQ.exists_corridorVisitEmbedding_eq_of_mem_P P qb hqbP
  have hABadj : G.Adj A B := by
    exact P.adj_getVert_succ hiData.1
  have hqdist : Nat.dist (qa : ℕ) (qb : ℕ) = 1 := by
    rw [← hQ.dist_eq_natDist_support_idxOf hAq hBq]
    exact dist_eq_one_iff_adj.mpr hABadj
  have hjne : ja ≠ jb := by
    have hqne : qa ≠ qb := by
      intro h
      have hval : (qa : ℕ) = (qb : ℕ) := congrArg Fin.val h
      rw [hval] at hqdist
      simp at hqdist
    intro hj
    apply hqne
    calc
      qa = corridorVisitEmbedding P Q ja := hja.symm
      _ = corridorVisitEmbedding P Q jb := by rw [hj]
      _ = qb := hjb
  have hvisitA : (corridorVisitVertices P Q).get ja = A := by
    rw [corridorVisitEmbedding_get, hja, hgetA]
  have hvisitB : (corridorVisitVertices P Q).get jb = B := by
    rw [corridorVisitEmbedding_get, hjb, hgetB]
  have hcoordA : corridorVisitIndexAt P Q ja = i := by
    rw [corridorVisitIndexAt, hvisitA]
    exact hP.support_idxOf_getVert hiData.1.le
  have hcoordB : corridorVisitIndexAt P Q jb = i + 1 := by
    rw [corridorVisitIndexAt, hvisitB]
    exact hP.support_idxOf_getVert (by omega)
  rcases lt_or_gt_of_ne hjne with hjab | hjba
  · have himage : (corridorVisitEmbedding P Q jb : ℕ) =
        (corridorVisitEmbedding P Q ja : ℕ) + 1 := by
      have hmap := (corridorVisitEmbedding P Q).strictMono hjab
      rw [hja, hjb] at hmap ⊢
      unfold Nat.dist at hqdist
      omega
    have hjSucc : (jb : ℕ) = (ja : ℕ) + 1 :=
      Fin.val_eq_add_one_of_orderEmbedding_image_eq_add_one
        (corridorVisitEmbedding P Q) hjab himage
    let t : CorridorTransition P Q := ⟨ja.1, by omega⟩
    have hstart : corridorTransitionStart P Q t = ja := by
      apply Fin.ext
      simp [corridorTransitionStart, t]
    have hend : corridorTransitionEnd P Q t = jb := by
      apply Fin.ext
      simpa [corridorTransitionEnd, t] using hjSucc.symm
    refine ⟨t, ?_, ?_⟩
    · rw [corridorTransitionGap, hstart, hend, hcoordA, hcoordB]
      simp [Nat.dist]
    · rw [corridorTransitionGapEdges, hstart, hend, hcoordA, hcoordB]
      simp [i]
  · have himage : (corridorVisitEmbedding P Q ja : ℕ) =
        (corridorVisitEmbedding P Q jb : ℕ) + 1 := by
      have hmap := (corridorVisitEmbedding P Q).strictMono hjba
      rw [hja, hjb] at hmap ⊢
      unfold Nat.dist at hqdist
      omega
    have hjSucc : (ja : ℕ) = (jb : ℕ) + 1 :=
      Fin.val_eq_add_one_of_orderEmbedding_image_eq_add_one
        (corridorVisitEmbedding P Q) hjba himage
    let t : CorridorTransition P Q := ⟨jb.1, by omega⟩
    have hstart : corridorTransitionStart P Q t = jb := by
      apply Fin.ext
      simp [corridorTransitionStart, t]
    have hend : corridorTransitionEnd P Q t = ja := by
      apply Fin.ext
      simpa [corridorTransitionEnd, t] using hjSucc.symm
    refine ⟨t, ?_, ?_⟩
    · rw [corridorTransitionGap, hstart, hend, hcoordA, hcoordB]
      simp [Nat.dist]
    · rw [corridorTransitionGapEdges, hstart, hend, hcoordA, hcoordB]
      simp [i]

/-- Distinct transition gap intervals are edge-disjoint.  This is the exact
finite-set form of the monotone-visit disjointness used in the packing
argument. -/
theorem corridorTransitionGapEdges_disjoint
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (htwo : 2 ≤ (commonVertices P Q).card)
    {t u : CorridorTransition P Q} (htu : t ≠ u) :
    Disjoint (corridorTransitionGapEdges P Q t)
      (corridorTransitionGapEdges P Q u) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hxt hxu
  rcases lt_or_gt_of_ne htu with htu' | hut'
  · have hEndStart : corridorTransitionEnd P Q t ≤
        corridorTransitionStart P Q u := by
      apply Fin.mk_le_mk.mpr
      simp [corridorTransitionEnd, corridorTransitionStart]
      exact htu'
    rcases hP.strictMono_or_strictAnti_corridorVisitIndexAt hQ htwo with
      hinc | hdec
    · have htOrient := hinc (corridorTransitionStart_lt_end P Q t)
      have huOrient := hinc (corridorTransitionStart_lt_end P Q u)
      have hmiddle := hinc.monotone hEndStart
      simp only [corridorTransitionGapEdges, Finset.mem_Ico] at hxt hxu
      omega
    · have htOrient := hdec (corridorTransitionStart_lt_end P Q t)
      have huOrient := hdec (corridorTransitionStart_lt_end P Q u)
      have hmiddle := hdec.antitone hEndStart
      simp only [corridorTransitionGapEdges, Finset.mem_Ico] at hxt hxu
      omega
  · have hEndStart : corridorTransitionEnd P Q u ≤
        corridorTransitionStart P Q t := by
      apply Fin.mk_le_mk.mpr
      simp [corridorTransitionEnd, corridorTransitionStart]
      exact hut'
    rcases hP.strictMono_or_strictAnti_corridorVisitIndexAt hQ htwo with
      hinc | hdec
    · have htOrient := hinc (corridorTransitionStart_lt_end P Q t)
      have huOrient := hinc (corridorTransitionStart_lt_end P Q u)
      have hmiddle := hinc.monotone hEndStart
      simp only [corridorTransitionGapEdges, Finset.mem_Ico] at hxt hxu
      omega
    · have htOrient := hdec (corridorTransitionStart_lt_end P Q t)
      have huOrient := hdec (corridorTransitionStart_lt_end P Q u)
      have hmiddle := hdec.antitone hEndStart
      simp only [corridorTransitionGapEdges, Finset.mem_Ico] at hxt hxu
      omega

/-! ## Exact ride-transition counting -/

/-- Consecutive common-visit transitions with unit corridor gap. -/
abbrev UnitCorridorTransition [DecidableEq V]
    {G : SimpleGraph V} {w x₀ y z : V}
    (P : G.Walk w x₀) (Q : G.Walk y z) :=
  {t : CorridorTransition P Q // corridorTransitionGap P Q t = 1}

noncomputable def unitTransitionRiddenIndex
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q) :
    UnitCorridorTransition P Q → RiddenCorridorEdgeIndex P Q := by
  classical
  intro t
  exact Classical.choose
    (hP.exists_riddenIndex_of_transitionGap_eq_one hQ t.1 t.2)

theorem unitTransition_gapEdges_eq_singleton
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (t : UnitCorridorTransition P Q) :
    corridorTransitionGapEdges P Q t.1 =
      {(unitTransitionRiddenIndex hP hQ t).1} := by
  classical
  exact (Classical.choose_spec
    (hP.exists_riddenIndex_of_transitionGap_eq_one hQ t.1 t.2)).2

theorem unitTransitionRiddenIndex_injective
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (htwo : 2 ≤ (commonVertices P Q).card) :
    Function.Injective (unitTransitionRiddenIndex hP hQ) := by
  classical
  intro t u htu
  apply Subtype.ext
  by_contra hne
  have hdisj := corridorTransitionGapEdges_disjoint hP hQ htwo hne
  have htSet := unitTransition_gapEdges_eq_singleton hP hQ t
  have huSet := unitTransition_gapEdges_eq_singleton hP hQ u
  have hval : (unitTransitionRiddenIndex hP hQ t).1 =
      (unitTransitionRiddenIndex hP hQ u).1 := congrArg Subtype.val htu
  have hxT : (unitTransitionRiddenIndex hP hQ t).1 ∈
      corridorTransitionGapEdges P Q t.1 := by simp [htSet]
  have hxU : (unitTransitionRiddenIndex hP hQ t).1 ∈
      corridorTransitionGapEdges P Q u.1 := by simp [huSet, hval]
  exact ((Finset.disjoint_left.mp hdisj hxT) hxU).elim

noncomputable def riddenIndexTransition
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q) :
    RiddenCorridorEdgeIndex P Q → UnitCorridorTransition P Q := by
  classical
  intro i
  let hex := hP.exists_transition_of_riddenIndex hQ i
  exact ⟨Classical.choose hex, (Classical.choose_spec hex).1⟩

theorem riddenIndexTransition_gapEdges_eq_singleton
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (i : RiddenCorridorEdgeIndex P Q) :
    corridorTransitionGapEdges P Q (riddenIndexTransition hP hQ i).1 =
      {i.1} := by
  classical
  exact (Classical.choose_spec
    (hP.exists_transition_of_riddenIndex hQ i)).2

theorem riddenIndexTransition_injective
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q) :
    Function.Injective (riddenIndexTransition hP hQ) := by
  classical
  intro i j hij
  apply Subtype.ext
  have hiSet := riddenIndexTransition_gapEdges_eq_singleton hP hQ i
  have hjSet := riddenIndexTransition_gapEdges_eq_singleton hP hQ j
  rw [hij] at hiSet
  have hsingle : ({i.1} : Finset ℕ) = {j.1} := hiSet.symm.trans hjSet
  simpa using hsingle

/-- Unit transitions and actually ridden corridor coordinates have the same
finite cardinality. -/
theorem card_unitCorridorTransition_eq_ridden
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (htwo : 2 ≤ (commonVertices P Q).card) :
    Fintype.card (UnitCorridorTransition P Q) =
      (riddenCorridorEdgeIndices P Q).card := by
  have hle := Fintype.card_le_of_injective
    (unitTransitionRiddenIndex hP hQ)
    (unitTransitionRiddenIndex_injective hP hQ htwo)
  have hge := Fintype.card_le_of_injective
    (riddenIndexTransition hP hQ)
    (riddenIndexTransition_injective hP hQ)
  have hriddenCard : Fintype.card (RiddenCorridorEdgeIndex P Q) =
      (riddenCorridorEdgeIndices P Q).card := by simp
  rw [hriddenCard] at hle hge
  omega

/-- The exact finite equivalence underlying the preceding cardinality
identity. -/
noncomputable def unitTransitionRiddenEquiv
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (htwo : 2 ≤ (commonVertices P Q).card) :
    UnitCorridorTransition P Q ≃ RiddenCorridorEdgeIndex P Q := by
  apply Equiv.ofBijective (unitTransitionRiddenIndex hP hQ)
  exact (Fintype.bijective_iff_injective_and_card _).2
    ⟨unitTransitionRiddenIndex_injective hP hQ htwo, by
      rw [card_unitCorridorTransition_eq_ridden hP hQ htwo]
      simp⟩

@[simp]
theorem unitTransitionRiddenEquiv_apply
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (htwo : 2 ≤ (commonVertices P Q).card)
    (t : UnitCorridorTransition P Q) :
    unitTransitionRiddenEquiv hP hQ htwo t =
      unitTransitionRiddenIndex hP hQ t := rfl

/-- The complementary transitions, necessarily of gap at least two. -/
abbrev ExcursionCorridorTransition [DecidableEq V]
    {G : SimpleGraph V} {w x₀ y z : V}
    (P : G.Walk w x₀) (Q : G.Walk y z) :=
  {t : CorridorTransition P Q // corridorTransitionGap P Q t ≠ 1}

theorem card_excursionCorridorTransition
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (htwo : 2 ≤ (commonVertices P Q).card) :
    Fintype.card (ExcursionCorridorTransition P Q) =
      (commonVertices P Q).card - 1 -
        (riddenCorridorEdgeIndices P Q).card := by
  calc
    Fintype.card (ExcursionCorridorTransition P Q) =
        Fintype.card (CorridorTransition P Q) -
          Fintype.card (UnitCorridorTransition P Q) := by
      exact Fintype.card_subtype_compl
        (fun t : CorridorTransition P Q => corridorTransitionGap P Q t = 1)
    _ = (commonVertices P Q).card - 1 -
        (riddenCorridorEdgeIndices P Q).card := by
      rw [card_unitCorridorTransition_eq_ridden hP hQ htwo]
      simp only [Fintype.card_fin]
      rw [hQ.length_corridorVisitVertices_eq_card_commonVertices]

theorem ExcursionCorridorTransition.gap_gt_one
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (t : ExcursionCorridorTransition P Q) :
    1 < corridorTransitionGap P Q t.1 := by
  have hpos := corridorTransitionGap_pos hP hQ t.1
  omega

/-- The canonical off-corridor component traversed by a non-unit
transition. -/
noncomputable def excursionTransitionComponent
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (t : ExcursionCorridorTransition P Q) : OffCorridorComponent P :=
  Classical.choose
    (hP.exists_excursionComponent_for_transition hQ t.1
      (t.gap_gt_one hP hQ))

theorem excursionTransition_gapEdges_subset_componentInterval
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (t : ExcursionCorridorTransition P Q) :
    corridorTransitionGapEdges P Q t.1 ⊆
      offCorridorComponentIntervalEdges P
        (excursionTransitionComponent hP hQ t) := by
  exact (Classical.choose_spec
    (hP.exists_excursionComponent_for_transition hQ t.1
      (t.gap_gt_one hP hQ))).2.2.1

/-- Every interior support vertex of a non-unit transition belongs to the
component selected for that transition.  This pins the selected component to
the one actually traversed by `Q`, rather than merely to some component whose
attachment interval happens to contain the same corridor gap. -/
theorem excursionTransition_interior_mem_component
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (t : ExcursionCorridorTransition P Q) (k : Fin Q.support.length)
    (hleft : corridorVisitEmbedding P Q
      (corridorTransitionStart P Q t.1) < k)
    (hright : k < corridorVisitEmbedding P Q
      (corridorTransitionEnd P Q t.1)) :
    Q.support.get k ∈ offCorridorComponentFinset
      (excursionTransitionComponent hP hQ t) := by
  exact (Classical.choose_spec
    (hP.exists_excursionComponent_for_transition hQ t.1
      (t.gap_gt_one hP hQ))).2.2.2 k hleft hright

/-- Assign each unit transition to the chosen owner of its ridden edge and
each non-unit transition to its actual excursion component. -/
noncomputable def canonicalTransitionOwner
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (hnonbridge : ∀ {a b : V}, s(a, b) ∈ P.edges →
      s(a, b) ∈ Q.edges → ¬G.IsBridge s(a, b)) :
    CorridorTransition P Q → OffCorridorComponent P := by
  classical
  intro t
  exact if ht : corridorTransitionGap P Q t = 1 then
    canonicalRiddenOwner hP hnonbridge
      (unitTransitionRiddenIndex hP hQ ⟨t, ht⟩)
  else excursionTransitionComponent hP hQ ⟨t, ht⟩

/-- Every transition's full gap interval lies inside the attachment interval
of its canonical owner. -/
theorem canonicalTransition_gapEdges_subset_ownerInterval
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (hnonbridge : ∀ {a b : V}, s(a, b) ∈ P.edges →
      s(a, b) ∈ Q.edges → ¬G.IsBridge s(a, b))
    (t : CorridorTransition P Q) :
    corridorTransitionGapEdges P Q t ⊆
      offCorridorComponentIntervalEdges P
        (canonicalTransitionOwner hP hQ hnonbridge t) := by
  classical
  by_cases ht : corridorTransitionGap P Q t = 1
  · let ut : UnitCorridorTransition P Q := ⟨t, ht⟩
    let ri := unitTransitionRiddenIndex hP hQ ut
    have hset := unitTransition_gapEdges_eq_singleton hP hQ ut
    have hmem := mem_offCorridorComponentIntervalEdges_of_coversIndex P
      (canonicalRiddenOwner hP hnonbridge ri)
      (canonicalRiddenOwner_covers hP hnonbridge ri)
    have howner : canonicalTransitionOwner hP hQ hnonbridge t =
        canonicalRiddenOwner hP hnonbridge ri := by
      simp [canonicalTransitionOwner, ht, ut, ri]
    rw [howner, hset]
    simpa using hmem
  · have howner : canonicalTransitionOwner hP hQ hnonbridge t =
        excursionTransitionComponent hP hQ
          (⟨t, ht⟩ : ExcursionCorridorTransition P Q) := by
      simp [canonicalTransitionOwner, ht]
    rw [howner]
    exact excursionTransition_gapEdges_subset_componentInterval hP hQ ⟨t, ht⟩

/-- The transitions assigned to one canonical component. -/
noncomputable def assignedTransitionFinset
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (owner : CorridorTransition P Q → OffCorridorComponent P)
    (C : OffCorridorComponent P) : Finset (CorridorTransition P Q) := by
  classical
  exact Finset.univ.filter fun t => owner t = C

/-- Union of the pairwise-disjoint transition gap intervals assigned to one
component. -/
noncomputable def assignedTransitionGapUnion
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (owner : CorridorTransition P Q → OffCorridorComponent P)
    (C : OffCorridorComponent P) : Finset ℕ := by
  classical
  exact (assignedTransitionFinset owner C).biUnion
    (corridorTransitionGapEdges P Q)

theorem card_assignedTransitionGapUnion
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (htwo : 2 ≤ (commonVertices P Q).card)
    (owner : CorridorTransition P Q → OffCorridorComponent P)
    (C : OffCorridorComponent P) :
    (assignedTransitionGapUnion owner C).card =
      ∑ t ∈ assignedTransitionFinset owner C,
        corridorTransitionGap P Q t := by
  classical
  rw [assignedTransitionGapUnion, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro t _
    exact card_corridorTransitionGapEdges P Q t
  · intro t _ht u _hu hne
    exact corridorTransitionGapEdges_disjoint hP hQ htwo hne

/-- The assigned transition union lies in the owner's component interval. -/
theorem canonical_assignedTransitionGapUnion_subset_componentInterval
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (hnonbridge : ∀ {a b : V}, s(a, b) ∈ P.edges →
      s(a, b) ∈ Q.edges → ¬G.IsBridge s(a, b))
    (C : OffCorridorComponent P) :
    assignedTransitionGapUnion
        (canonicalTransitionOwner hP hQ hnonbridge) C ⊆
      offCorridorComponentIntervalEdges P C := by
  classical
  rw [assignedTransitionGapUnion,
    Finset.biUnion_subset_iff_forall_subset]
  intro t ht
  have htOwner : canonicalTransitionOwner hP hQ hnonbridge t = C := by
    simpa [assignedTransitionFinset] using ht
  simpa [htOwner] using
    canonicalTransition_gapEdges_subset_ownerInterval hP hQ hnonbridge t

/-- Exact interval packing for the sum of all transition gap lengths
assigned to one component. -/
theorem canonical_sum_assignedTransitionGap_le_span
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (htwo : 2 ≤ (commonVertices P Q).card)
    (hnonbridge : ∀ {a b : V}, s(a, b) ∈ P.edges →
      s(a, b) ∈ Q.edges → ¬G.IsBridge s(a, b))
    (C : OffCorridorComponent P) :
    (∑ t ∈ assignedTransitionFinset
        (canonicalTransitionOwner hP hQ hnonbridge) C,
      corridorTransitionGap P Q t) ≤ offCorridorComponentSpan P C := by
  rw [← card_assignedTransitionGapUnion hP hQ htwo,
    ← card_offCorridorComponentIntervalEdges P C]
  exact Finset.card_le_card
    (canonical_assignedTransitionGapUnion_subset_componentInterval
      hP hQ hnonbridge C)

/-- Unit transitions assigned to one component, with the unit predicate
filtered first so the subtype equivalence is definitional. -/
noncomputable def canonicalAssignedUnitTransitions
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (hnonbridge : ∀ {a b : V}, s(a, b) ∈ P.edges →
      s(a, b) ∈ Q.edges → ¬G.IsBridge s(a, b))
    (C : OffCorridorComponent P) : Finset (CorridorTransition P Q) := by
  classical
  exact (Finset.univ.filter fun t => corridorTransitionGap P Q t = 1).filter
    fun t => canonicalTransitionOwner hP hQ hnonbridge t = C

/-- Non-unit transitions assigned to one component. -/
noncomputable def canonicalAssignedExcursionTransitions
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (hnonbridge : ∀ {a b : V}, s(a, b) ∈ P.edges →
      s(a, b) ∈ Q.edges → ¬G.IsBridge s(a, b))
    (C : OffCorridorComponent P) : Finset (CorridorTransition P Q) := by
  classical
  exact (Finset.univ.filter fun t => corridorTransitionGap P Q t ≠ 1).filter
    fun t => canonicalTransitionOwner hP hQ hnonbridge t = C

noncomputable def canonicalAssignedExcursionGap
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (hnonbridge : ∀ {a b : V}, s(a, b) ∈ P.edges →
      s(a, b) ∈ Q.edges → ¬G.IsBridge s(a, b))
    (C : OffCorridorComponent P) : ℕ :=
  ∑ t ∈ canonicalAssignedExcursionTransitions hP hQ hnonbridge C,
    corridorTransitionGap P Q t

/-- The total assigned gap splits into one edge per unit transition plus the
full gaps of the non-unit transitions. -/
theorem canonical_assignedUnitCard_add_excursionGap
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (hnonbridge : ∀ {a b : V}, s(a, b) ∈ P.edges →
      s(a, b) ∈ Q.edges → ¬G.IsBridge s(a, b))
    (C : OffCorridorComponent P) :
    (canonicalAssignedUnitTransitions hP hQ hnonbridge C).card +
        canonicalAssignedExcursionGap hP hQ hnonbridge C =
      ∑ t ∈ assignedTransitionFinset
          (canonicalTransitionOwner hP hQ hnonbridge) C,
        corridorTransitionGap P Q t := by
  classical
  let S := assignedTransitionFinset
    (canonicalTransitionOwner hP hQ hnonbridge) C
  let p : CorridorTransition P Q → Prop := fun t =>
    corridorTransitionGap P Q t = 1
  have hU : canonicalAssignedUnitTransitions hP hQ hnonbridge C =
      S.filter p := by
    ext t
    simp [canonicalAssignedUnitTransitions, S, p, assignedTransitionFinset,
      and_comm]
  have hE : canonicalAssignedExcursionTransitions hP hQ hnonbridge C =
      S.filter fun t => ¬p t := by
    ext t
    simp [canonicalAssignedExcursionTransitions, S, p,
      assignedTransitionFinset, and_comm]
  have hunit : (S.filter p).card =
      ∑ t ∈ S.filter p, corridorTransitionGap P Q t := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro t ht
    have := (Finset.mem_filter.mp ht).2
    exact this.symm
  rw [hU]
  unfold canonicalAssignedExcursionGap
  rw [hE, hunit]
  change (∑ t ∈ S.filter p, corridorTransitionGap P Q t) +
      ∑ t ∈ S.filter (fun t => ¬p t), corridorTransitionGap P Q t =
    ∑ t ∈ S, corridorTransitionGap P Q t
  exact Finset.sum_filter_add_sum_filter_not S p
    (corridorTransitionGap P Q)

/-- The number of unit transitions assigned to `C` is exactly the genuine
fiber count of ridden coordinates assigned to `C`. -/
theorem card_canonicalAssignedUnitTransitions_eq_assignedRiddenCount
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (htwo : 2 ≤ (commonVertices P Q).card)
    (hnonbridge : ∀ {a b : V}, s(a, b) ∈ P.edges →
      s(a, b) ∈ Q.edges → ¬G.IsBridge s(a, b))
    (C : OffCorridorComponent P) :
    (canonicalAssignedUnitTransitions hP hQ hnonbridge C).card =
      assignedRiddenCount (canonicalRiddenOwner hP hnonbridge) C := by
  classical
  let p : CorridorTransition P Q → Prop := fun t =>
    corridorTransitionGap P Q t = 1
  let q : CorridorTransition P Q → Prop := fun t =>
    canonicalTransitionOwner hP hQ hnonbridge t = C
  let qU : UnitCorridorTransition P Q → Prop := fun t =>
    canonicalRiddenOwner hP hnonbridge
      (unitTransitionRiddenIndex hP hQ t) = C
  let qR : RiddenCorridorEdgeIndex P Q → Prop := fun i =>
    canonicalRiddenOwner hP hnonbridge i = C
  let e := unitTransitionRiddenEquiv hP hQ htwo
  have hsource : Fintype.card {t : CorridorTransition P Q // p t ∧ q t} =
      (canonicalAssignedUnitTransitions hP hQ hnonbridge C).card := by
    let U := canonicalAssignedUnitTransitions hP hQ hnonbridge C
    let eU : {t : CorridorTransition P Q // p t ∧ q t} ≃ ↥U :=
      Equiv.subtypeEquiv (Equiv.refl _) (by
        intro t
        simp [U, canonicalAssignedUnitTransitions, p, q])
    calc
      Fintype.card {t : CorridorTransition P Q // p t ∧ q t} =
          Fintype.card ↥U := Fintype.card_congr eU
      _ = U.card := Fintype.card_coe U
  have hnest : Fintype.card {t : UnitCorridorTransition P Q // q t.1} =
      Fintype.card {t : CorridorTransition P Q // p t ∧ q t} :=
    Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter p q)
  have hpredU : Fintype.card {t : UnitCorridorTransition P Q // q t.1} =
      Fintype.card {t : UnitCorridorTransition P Q // qU t} := by
    apply Fintype.card_congr
    apply Equiv.subtypeEquiv (Equiv.refl _)
    intro t
    simp [q, qU, canonicalTransitionOwner, t.2]
  have hpredR : Fintype.card {t : UnitCorridorTransition P Q // qU t} =
      Fintype.card {i : RiddenCorridorEdgeIndex P Q // qR i} := by
    apply Fintype.card_congr
    apply Equiv.subtypeEquiv e
    intro t
    simp [e, qU, qR]
  have htarget : Fintype.card {i : RiddenCorridorEdgeIndex P Q // qR i} =
      assignedRiddenCount (canonicalRiddenOwner hP hnonbridge) C := by
    apply Fintype.subtype_card
  omega

/-- The exact interval packing field required by `OffCorridorLocalCharge`. -/
theorem canonical_assignedRidden_add_excursionGap_le_span
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (htwo : 2 ≤ (commonVertices P Q).card)
    (hnonbridge : ∀ {a b : V}, s(a, b) ∈ P.edges →
      s(a, b) ∈ Q.edges → ¬G.IsBridge s(a, b))
    (C : OffCorridorComponent P) :
    assignedRiddenCount (canonicalRiddenOwner hP hnonbridge) C +
        canonicalAssignedExcursionGap hP hQ hnonbridge C ≤
      offCorridorComponentSpan P C := by
  rw [← card_canonicalAssignedUnitTransitions_eq_assignedRiddenCount
    hP hQ htwo hnonbridge C,
    canonical_assignedUnitCard_add_excursionGap hP hQ hnonbridge C]
  exact canonical_sum_assignedTransitionGap_le_span
    hP hQ htwo hnonbridge C

noncomputable def canonicalAssignedExcursionCount
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (hnonbridge : ∀ {a b : V}, s(a, b) ∈ P.edges →
      s(a, b) ∈ Q.edges → ¬G.IsBridge s(a, b))
    (C : OffCorridorComponent P) : ℕ :=
  (canonicalAssignedExcursionTransitions hP hQ hnonbridge C).card

noncomputable def canonicalAssignedQExcCount
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (hnonbridge : ∀ {a b : V}, s(a, b) ∈ P.edges →
      s(a, b) ∈ Q.edges → ¬G.IsBridge s(a, b))
    (C : OffCorridorComponent P) : ℕ :=
  canonicalAssignedExcursionGap hP hQ hnonbridge C -
    canonicalAssignedExcursionCount hP hQ hnonbridge C

/-- Every non-unit transition has gap at least two, so the number of
excursions is at most their total gap. -/
theorem canonicalAssignedExcursionCount_le_gap
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (hnonbridge : ∀ {a b : V}, s(a, b) ∈ P.edges →
      s(a, b) ∈ Q.edges → ¬G.IsBridge s(a, b))
    (C : OffCorridorComponent P) :
    canonicalAssignedExcursionCount hP hQ hnonbridge C ≤
      canonicalAssignedExcursionGap hP hQ hnonbridge C := by
  rw [canonicalAssignedExcursionCount, canonicalAssignedExcursionGap,
    Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro t ht
  have hne : corridorTransitionGap P Q t ≠ 1 := by
    have htData : corridorTransitionGap P Q t ≠ 1 ∧
        canonicalTransitionOwner hP hQ hnonbridge t = C := by
      simpa [canonicalAssignedExcursionTransitions] using ht
    exact htData.1
  have hpos := corridorTransitionGap_pos hP hQ t
  omega

theorem two_mul_canonicalAssignedExcursionCount_le_gap
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (hnonbridge : ∀ {a b : V}, s(a, b) ∈ P.edges →
      s(a, b) ∈ Q.edges → ¬G.IsBridge s(a, b))
    (C : OffCorridorComponent P) :
    2 * canonicalAssignedExcursionCount hP hQ hnonbridge C ≤
      canonicalAssignedExcursionGap hP hQ hnonbridge C := by
  let S := canonicalAssignedExcursionTransitions hP hQ hnonbridge C
  have hcard : 2 * S.card = ∑ _t ∈ S, 2 := by
    simp [Nat.mul_comm]
  rw [canonicalAssignedExcursionCount, canonicalAssignedExcursionGap, hcard]
  apply Finset.sum_le_sum
  intro t ht
  have htData : corridorTransitionGap P Q t ≠ 1 ∧
      canonicalTransitionOwner hP hQ hnonbridge t = C := by
    simpa [S, canonicalAssignedExcursionTransitions] using ht
  have hpos := corridorTransitionGap_pos hP hQ t
  omega

/-- A zero internal-excursion count forces zero excursions. -/
theorem canonicalAssignedExcursionCount_eq_zero_of_qexc_eq_zero
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (hnonbridge : ∀ {a b : V}, s(a, b) ∈ P.edges →
      s(a, b) ∈ Q.edges → ¬G.IsBridge s(a, b))
    (C : OffCorridorComponent P)
    (hqexc : canonicalAssignedQExcCount hP hQ hnonbridge C = 0) :
    canonicalAssignedExcursionCount hP hQ hnonbridge C = 0 := by
  have htwo := two_mul_canonicalAssignedExcursionCount_le_gap
    hP hQ hnonbridge C
  have hsub : canonicalAssignedExcursionGap hP hQ hnonbridge C ≤
      canonicalAssignedExcursionCount hP hQ hnonbridge C := by
    exact Nat.sub_eq_zero_iff_le.mp (by
      simpa [canonicalAssignedQExcCount] using hqexc)
  omega

/-! ## Exceptional-tail toolkit -/

/-- A support position lying strictly between the first and last common
visits and off the corridor lies inside a unique non-unit transition. -/
theorem IsGeodesic.exists_excursionTransition_around_interior_position
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (htwo : 2 ≤ (commonVertices P Q).card)
    (k : Fin Q.support.length) (hkOff : Q.support.get k ∉ P.support)
    (hfirst : corridorVisitEmbedding P Q
        ⟨0, by
          rw [hQ.length_corridorVisitVertices_eq_card_commonVertices]
          omega⟩ < k)
    (hlast : k < corridorVisitEmbedding P Q
        ⟨(corridorVisitVertices P Q).length - 1, by
          rw [hQ.length_corridorVisitVertices_eq_card_commonVertices]
          omega⟩) :
    ∃ t : ExcursionCorridorTransition P Q,
      corridorVisitEmbedding P Q
          (corridorTransitionStart P Q t.1) < k ∧
        k < corridorVisitEmbedding P Q
          (corridorTransitionEnd P Q t.1) := by
  classical
  let n := (corridorVisitVertices P Q).length
  have hn : 2 ≤ n := by
    dsimp [n]
    rw [hQ.length_corridorVisitVertices_eq_card_commonVertices]
    exact htwo
  let f : Fin n ↪o Fin Q.support.length := corridorVisitEmbedding P Q
  let last : Fin n := ⟨n - 1, by omega⟩
  let pred : Fin n → Prop := fun j => k < f j
  have hex : ∃ j : Fin n, pred j := by
    refine ⟨last, ?_⟩
    simpa [f, last, n] using hlast
  let j : Fin n := Fin.find pred hex
  have hjPred : pred j := Fin.find_spec hex
  have hjPos : 0 < (j : ℕ) := by
    by_contra h
    let zero : Fin n := ⟨0, by omega⟩
    have hj0 : j = zero := by
      apply Fin.ext
      dsimp [zero]
      omega
    rw [hj0] at hjPred
    have : f zero < k := by simpa [f, n, zero] using hfirst
    exact (not_lt_of_ge this.le) hjPred
  let i : Fin n := ⟨(j : ℕ) - 1, by omega⟩
  have hij : i < j := by
    apply Fin.mk_lt_mk.mpr
    change (j : ℕ) - 1 < (j : ℕ)
    omega
  have hiNotPred : ¬pred i := Fin.find_min hex hij
  have hfiLe : f i ≤ k := by
    exact le_of_not_gt hiNotPred
  have hfiNe : f i ≠ k := by
    intro hik
    apply hkOff
    have hiMem := corridorVisitVertex_mem_supports P Q i
    have hget : Q.support.get (f i) =
        (corridorVisitVertices P Q).get i := by
      simpa [f, n] using (corridorVisitEmbedding_get P Q i).symm
    rw [← hik, hget]
    exact hiMem.1
  have hfiLt : f i < k := lt_of_le_of_ne hfiLe hfiNe
  let t : CorridorTransition P Q := ⟨(i : ℕ), by
    change (i : ℕ) < n - 1
    dsimp [i]
    omega⟩
  have hstart : corridorTransitionStart P Q t = i := by
    apply Fin.ext
    rfl
  have hend : corridorTransitionEnd P Q t = j := by
    apply Fin.ext
    dsimp [corridorTransitionEnd, t, i]
    omega
  have hleft : corridorVisitEmbedding P Q
      (corridorTransitionStart P Q t) < k := by
    simpa [f, n, hstart] using hfiLt
  have hright : k < corridorVisitEmbedding P Q
      (corridorTransitionEnd P Q t) := by
    simpa [pred, f, n, hend] using hjPred
  have hgapNe : corridorTransitionGap P Q t ≠ 1 := by
    have hgap := corridorTransitionGap_eq_Q_index_sub hP hQ t
    have hstartEnd :
        (corridorVisitEmbedding P Q
            (corridorTransitionStart P Q t) : ℕ) + 2 ≤
          corridorVisitEmbedding P Q (corridorTransitionEnd P Q t) := by
      omega
    omega
  exact ⟨⟨t, hgapNe⟩, hleft, hright⟩

/-- Zero assigned excursion count excludes vertices of that component from
the open support interval between the first and last common visits. -/
theorem no_component_vertex_between_extreme_visits_of_qexc_eq_zero
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (htwo : 2 ≤ (commonVertices P Q).card)
    (hnonbridge : ∀ {a b : V}, s(a, b) ∈ P.edges →
      s(a, b) ∈ Q.edges → ¬G.IsBridge s(a, b))
    (C : OffCorridorComponent P)
    (hqexc : canonicalAssignedQExcCount hP hQ hnonbridge C = 0)
    (k : Fin Q.support.length)
    (hkC : Q.support.get k ∈ offCorridorComponentFinset C) :
    ¬(corridorVisitEmbedding P Q
          ⟨0, by
            rw [hQ.length_corridorVisitVertices_eq_card_commonVertices]
            omega⟩ < k ∧
        k < corridorVisitEmbedding P Q
          ⟨(corridorVisitVertices P Q).length - 1, by
            rw [hQ.length_corridorVisitVertices_eq_card_commonVertices]
            omega⟩) := by
  classical
  intro hkBetween
  have hkCSet : Q.support.get k ∈ C :=
    (mem_offCorridorComponentFinset C).1 hkC
  have hkOffFin : Q.support.get k ∉ supportFinset P :=
    C.notMem_of_mem hkCSet
  have hkOff : Q.support.get k ∉ P.support := by
    simpa [supportFinset] using hkOffFin
  obtain ⟨t, hleft, hright⟩ :=
    hP.exists_excursionTransition_around_interior_position hQ htwo k hkOff
      hkBetween.1 hkBetween.2
  let D := excursionTransitionComponent hP hQ t
  have hkD : Q.support.get k ∈ offCorridorComponentFinset D :=
    excursionTransition_interior_mem_component hP hQ t k hleft hright
  have hDC : D = C := by
    by_contra hne
    have hdisj : Disjoint (D : Set V) (C : Set V) :=
      ComponentCompl.pairwise_disjoint hne
    have hkDSet : Q.support.get k ∈ D :=
      (mem_offCorridorComponentFinset D).1 hkD
    exact (Set.disjoint_left.mp hdisj hkDSet hkCSet).elim
  have howner : canonicalTransitionOwner hP hQ hnonbridge t.1 = C := by
    simp [canonicalTransitionOwner, t.2, D, hDC]
  have htMem : t.1 ∈
      canonicalAssignedExcursionTransitions hP hQ hnonbridge C := by
    simp [canonicalAssignedExcursionTransitions, t.2, howner]
  have hcount0 := canonicalAssignedExcursionCount_eq_zero_of_qexc_eq_zero
    hP hQ hnonbridge C hqexc
  have hempty :
      canonicalAssignedExcursionTransitions hP hQ hnonbridge C = ∅ := by
    apply Finset.card_eq_zero.mp
    exact hcount0
  rw [hempty] at htMem
  simp at htMem

/-- Consequently every component vertex on `Q` lies strictly in the initial
or final off-corridor tail. -/
theorem component_vertex_lies_in_extreme_tail_of_qexc_eq_zero
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (htwo : 2 ≤ (commonVertices P Q).card)
    (hnonbridge : ∀ {a b : V}, s(a, b) ∈ P.edges →
      s(a, b) ∈ Q.edges → ¬G.IsBridge s(a, b))
    (C : OffCorridorComponent P)
    (hqexc : canonicalAssignedQExcCount hP hQ hnonbridge C = 0)
    (k : Fin Q.support.length)
    (hkC : Q.support.get k ∈ offCorridorComponentFinset C) :
    k < corridorVisitEmbedding P Q
        ⟨0, by
          rw [hQ.length_corridorVisitVertices_eq_card_commonVertices]
          omega⟩ ∨
      corridorVisitEmbedding P Q
          ⟨(corridorVisitVertices P Q).length - 1, by
            rw [hQ.length_corridorVisitVertices_eq_card_commonVertices]
            omega⟩ < k := by
  classical
  let firstVisit : Fin (corridorVisitVertices P Q).length := ⟨0, by
    rw [hQ.length_corridorVisitVertices_eq_card_commonVertices]
    omega⟩
  let first : Fin Q.support.length := corridorVisitEmbedding P Q firstVisit
  let lastVisit : Fin (corridorVisitVertices P Q).length :=
    ⟨(corridorVisitVertices P Q).length - 1, by
      rw [hQ.length_corridorVisitVertices_eq_card_commonVertices]
      omega⟩
  let last : Fin Q.support.length := corridorVisitEmbedding P Q lastVisit
  have hfirstLast : first ≤ last := by
    apply (corridorVisitEmbedding P Q).monotone
    apply Fin.mk_le_mk.mpr
    dsimp [firstVisit, lastVisit]
    omega
  have hkNeFirst : k ≠ first := by
    intro hk
    have hkP : Q.support.get k ∈ P.support := by
      rw [hk]
      have hget : Q.support.get first =
          (corridorVisitVertices P Q).get firstVisit := by
        exact (corridorVisitEmbedding_get P Q firstVisit).symm
      rw [hget]
      exact (corridorVisitVertex_mem_supports P Q
        firstVisit).1
    have hkCSet : Q.support.get k ∈ C :=
      (mem_offCorridorComponentFinset C).1 hkC
    exact C.notMem_of_mem hkCSet (by simpa [supportFinset] using hkP)
  have hkNeLast : k ≠ last := by
    intro hk
    have hkP : Q.support.get k ∈ P.support := by
      rw [hk]
      dsimp [last]
      change Q.support.get (corridorVisitEmbedding P Q lastVisit) ∈ P.support
      have hget : Q.support.get (corridorVisitEmbedding P Q lastVisit) =
          (corridorVisitVertices P Q).get lastVisit := by
        exact (corridorVisitEmbedding_get P Q lastVisit).symm
      rw [hget]
      exact (corridorVisitVertex_mem_supports P Q lastVisit).1
    have hkCSet : Q.support.get k ∈ C :=
      (mem_offCorridorComponentFinset C).1 hkC
    exact C.notMem_of_mem hkCSet (by simpa [supportFinset] using hkP)
  have hnotBetween :=
    no_component_vertex_between_extreme_visits_of_qexc_eq_zero
      hP hQ htwo hnonbridge C hqexc k hkC
  dsimp [first, firstVisit, last, lastVisit] at hfirstLast hkNeFirst hkNeLast ⊢
  by_contra h
  push_neg at h
  apply hnotBetween
  constructor <;> omega

/-- If a component has no vertices unused by `Q`, every one of its vertices
belongs to the support of `Q`. -/
theorem mem_Q_support_of_mem_component_of_RCount_eq_zero
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} (Q : G.Walk y z) (C : OffCorridorComponent P)
    (hr : offCorridorComponentRCount Q C = 0) {x : V}
    (hx : x ∈ offCorridorComponentFinset C) : x ∈ Q.support := by
  classical
  have hempty : offCorridorComponentFinset C ∩
      (Finset.univ \ supportFinset Q) = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [offCorridorComponentRCount] using hr
  by_contra hxQ
  have hxBad : x ∈ offCorridorComponentFinset C ∩
      (Finset.univ \ supportFinset Q) := by
    simp [hx, hxQ, supportFinset]
  rw [hempty] at hxBad
  simp at hxBad

/-- Two vertices of one finite off-corridor component have graph distance
plus one at most the component cardinality. -/
theorem offCorridorComponent_dist_add_one_le_card
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v x y : V}
    {P : G.Walk u v} (C : OffCorridorComponent P)
    (hx : x ∈ offCorridorComponentFinset C)
    (hy : y ∈ offCorridorComponentFinset C) :
    G.dist x y + 1 ≤ (offCorridorComponentFinset C).card := by
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
  obtain ⟨W, hW⟩ := C.connected_toSimpleGraph.exists_isPath ⟨x', hx'⟩ ⟨y', hy'⟩
  let Woff := W.map C.toSimpleGraph_hom
  let W' : G.Walk x y :=
    (Woff.map (Embedding.induce (supportFinset P : Set V)ᶜ).toHom).copy rfl rfl
  have hWoff : Woff.IsPath :=
    Walk.map_isPath_of_injective Subtype.val_injective hW
  have hW' : W'.IsPath := by
    simpa [W'] using Walk.map_isPath_of_injective Subtype.val_injective hWoff
  have hW'C : ∀ a ∈ W'.support, a ∈ offCorridorComponentFinset C := by
    intro a ha
    change a ∈
      ((Woff.map (Embedding.induce (supportFinset P : Set V)ᶜ).toHom).copy
        rfl rfl).support at ha
    simp only [Walk.support_copy, Walk.support_map] at ha
    obtain ⟨aOff, haOff, rfl⟩ := List.mem_map.mp ha
    change aOff ∈ (W.map C.toSimpleGraph_hom).support at haOff
    rw [Walk.support_map] at haOff
    obtain ⟨aC, _, haC⟩ := List.mem_map.mp haOff
    have hval : aOff = aC.val := by simpa using haC.symm
    rw [hval]
    have hcomp : G.componentComplMk aC.val.prop = C :=
      (ConnectedComponent.mem_supp_iff C aC.val).1 aC.prop
    exact (mem_offCorridorComponentFinset C).2
      (ComponentCompl.mem_supp_iff.mpr ⟨aC.val.prop, hcomp⟩)
  have hsupport : W'.support.toFinset ⊆ offCorridorComponentFinset C := by
    intro a ha
    exact hW'C a (by simpa using ha)
  have hcard : W'.length + 1 ≤ (offCorridorComponentFinset C).card := by
    rw [← Walk.length_support,
      ← List.toFinset_card_of_nodup hW'.support_nodup]
    exact Finset.card_le_card hsupport
  have hdist := dist_le W'
  omega

/-- The actual ridden corridor coordinates assigned to one owner, projected
back from their subtype to natural-number coordinates. -/
noncomputable def assignedRiddenIndexFinset
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (owner : RiddenCorridorEdgeIndex P Q → OffCorridorComponent P)
    (C : OffCorridorComponent P) : Finset ℕ := by
  classical
  exact (Finset.univ.filter fun i => owner i = C).image Subtype.val

theorem card_assignedRiddenIndexFinset
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (owner : RiddenCorridorEdgeIndex P Q → OffCorridorComponent P)
    (C : OffCorridorComponent P) :
    (assignedRiddenIndexFinset owner C).card = assignedRiddenCount owner C := by
  classical
  rw [assignedRiddenIndexFinset, assignedRiddenCount,
    Finset.card_image_of_injective _ Subtype.val_injective]

theorem canonicalAssignedRiddenIndexFinset_subset_componentInterval
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P)
    (hnonbridge : ∀ {a b : V}, s(a, b) ∈ P.edges →
      s(a, b) ∈ Q.edges → ¬G.IsBridge s(a, b))
    (C : OffCorridorComponent P) :
    assignedRiddenIndexFinset (canonicalRiddenOwner hP hnonbridge) C ⊆
      offCorridorComponentIntervalEdges P C := by
  classical
  intro i hi
  obtain ⟨ri, hri, rfl⟩ := Finset.mem_image.mp hi
  have howner : canonicalRiddenOwner hP hnonbridge ri = C := by
    simpa using (Finset.mem_filter.mp hri).2
  rw [← howner]
  exact mem_offCorridorComponentIntervalEdges_of_coversIndex P _
    (canonicalRiddenOwner_covers hP hnonbridge ri)

/-! ## Exact final boundary: exceptional tails -/

/-- The one graph lemma still needed after the ordered-transition and
packing construction: in a component with no internal excursion vertices
and no vertices unused by `Q`, the assigned ridden fiber is bounded by the
actual `Q`-vertex count of that component.

This is precisely the repaired initial/final-tail inequality `(4)` in the
paper audit. -/
def CanonicalExceptionalTailBound
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (hnonbridge : ∀ {a b : V}, s(a, b) ∈ P.edges →
      s(a, b) ∈ Q.edges → ¬G.IsBridge s(a, b)) : Prop :=
  ∀ C : OffCorridorComponent P,
    canonicalAssignedQExcCount hP hQ hnonbridge C = 0 →
    offCorridorComponentRCount Q C = 0 →
    assignedRiddenCount (canonicalRiddenOwner hP hnonbridge) C ≤
      offCorridorComponentQCount Q C

/-- The repaired exceptional-tail inequality.  Tightness in both interval
packing bounds would force the two extreme attachment coordinates to be
ridden.  Since every component vertex is then on `Q` and zero `qexc`
excludes an internal excursion, the two attachment edges have incompatible
positions in the initial/final tails. -/
theorem canonicalExceptionalTailBound
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (htwo : 2 ≤ (commonVertices P Q).card)
    (hnonbridge : ∀ {a b : V}, s(a, b) ∈ P.edges →
      s(a, b) ∈ Q.edges → ¬G.IsBridge s(a, b)) :
    CanonicalExceptionalTailBound hP hQ hnonbridge := by
  classical
  intro C hqexc hr
  let qC := offCorridorComponentQCount Q C
  let rides := assignedRiddenCount (canonicalRiddenOwner hP hnonbridge) C
  let gap := canonicalAssignedExcursionGap hP hQ hnonbridge C
  let span := offCorridorComponentSpan P C
  have hCpos : 0 < (offCorridorComponentFinset C).card := by
    obtain ⟨c, hc⟩ := C.nonempty
    exact Finset.card_pos.mpr ⟨c, (mem_offCorridorComponentFinset C).2 hc⟩
  have hcardC : (offCorridorComponentFinset C).card = qC := by
    have hpartition := offCorridorComponentQCount_add_RCount Q C
    omega
  have hqpos : 0 < qC := by omega
  have hpack : rides + gap ≤ span := by
    simpa [rides, gap, span] using
      canonical_assignedRidden_add_excursionGap_le_span
        hP hQ htwo hnonbridge C
  have hspanCard : span ≤ qC + 1 := by
    have hspan := hP.offCorridorComponentSpan_le_card_add_one C
    simpa [span, hcardC] using hspan
  by_contra hgoal
  have hrideLower : qC + 1 ≤ rides := by omega
  have hrideEq : rides = qC + 1 := by omega
  have hspanEq : span = qC + 1 := by omega
  have hgapEq : gap = 0 := by omega

  let S := assignedRiddenIndexFinset
    (canonicalRiddenOwner hP hnonbridge) C
  let I := offCorridorComponentIntervalEdges P C
  have hSI : S ⊆ I := by
    simpa [S, I] using
      canonicalAssignedRiddenIndexFinset_subset_componentInterval
        hP hnonbridge C
  have hScard : S.card = rides := by
    simpa [S, rides] using card_assignedRiddenIndexFinset
      (canonicalRiddenOwner hP hnonbridge) C
  have hIcard : I.card = span := by
    simpa [I, span] using card_offCorridorComponentIntervalEdges P C
  have hSIeq : S = I := by
    apply Finset.eq_of_subset_of_card_le hSI
    omega

  let A := offCorridorAttachmentIndices P C
  have hA : A.Nonempty := by
    by_contra hAempty
    have hspanZero : span = 0 := by
      simp [span, offCorridorComponentSpan, A, hAempty]
    omega
  let l := A.min' hA
  let h := A.max' hA
  have hlA : l ∈ A := A.min'_mem hA
  have hhA : h ∈ A := A.max'_mem hA
  have hlh : l ≤ h := A.min'_le_max' hA
  have hspanLH : span = h - l := by
    simp [span, offCorridorComponentSpan, A, hA, l, h]
  have hlth : l < h := by omega
  have hIeq : I = Finset.Ico l h := by
    simp [I, offCorridorComponentIntervalEdges, A, hA, l, h]
  have hlI : l ∈ I := by
    rw [hIeq]
    exact Finset.mem_Ico.mpr ⟨le_rfl, hlth⟩
  have hhpredI : h - 1 ∈ I := by
    rw [hIeq]
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hlS : l ∈ S := by simpa [hSIeq] using hlI
  have hhpredS : h - 1 ∈ S := by simpa [hSIeq] using hhpredI
  have hlRide : l ∈ riddenCorridorEdgeIndices P Q := by
    change l ∈ (Finset.univ.filter fun i : RiddenCorridorEdgeIndex P Q =>
      canonicalRiddenOwner hP hnonbridge i = C).image Subtype.val at hlS
    obtain ⟨ri, _hri, hriVal⟩ := Finset.mem_image.mp hlS
    simpa [← hriVal] using ri.2
  have hhpredRide : h - 1 ∈ riddenCorridorEdgeIndices P Q := by
    change h - 1 ∈ (Finset.univ.filter fun i : RiddenCorridorEdgeIndex P Q =>
      canonicalRiddenOwner hP hnonbridge i = C).image Subtype.val at hhpredS
    obtain ⟨ri, _hri, hriVal⟩ := Finset.mem_image.mp hhpredS
    simpa [← hriVal] using ri.2

  have hlCommon := (ridden_index_mem_common_and_succ P Q hlRide).1
  have hhCommonRaw :=
    (ridden_index_mem_common_and_succ P Q hhpredRide).2
  have hhSucc : h - 1 + 1 = h := by omega
  have hhCommon : h ∈ commonCorridorIndices P Q := by
    simpa [hhSucc] using hhCommonRaw
  have huLQ : P.getVert l ∈ Q.support :=
    (mem_commonCorridorIndices P Q l).1 hlCommon |>.2
  have huHQ : P.getVert h ∈ Q.support :=
    (mem_commonCorridorIndices P Q h).1 hhCommon |>.2
  have huLP : P.getVert l ∈ P.support := P.getVert_mem_support l
  have huHP : P.getVert h ∈ P.support := P.getVert_mem_support h

  have hlData := (mem_offCorridorAttachmentIndices P C l).1 (by
    simpa [A] using hlA)
  have hhData := (mem_offCorridorAttachmentIndices P C h).1 (by
    simpa [A] using hhA)
  obtain ⟨hlLen, cL, hcLC, hcLAdj⟩ := hlData
  obtain ⟨hhLen, cH, hcHC, hcHAdj⟩ := hhData
  have hcLQ : cL ∈ Q.support :=
    mem_Q_support_of_mem_component_of_RCount_eq_zero Q C hr hcLC
  have hcHQ : cH ∈ Q.support :=
    mem_Q_support_of_mem_component_of_RCount_eq_zero Q C hr hcHC

  let kcL : Fin Q.support.length :=
    ⟨Q.support.idxOf cL, List.idxOf_lt_length_of_mem hcLQ⟩
  let kcH : Fin Q.support.length :=
    ⟨Q.support.idxOf cH, List.idxOf_lt_length_of_mem hcHQ⟩
  let kuL : Fin Q.support.length :=
    ⟨Q.support.idxOf (P.getVert l), List.idxOf_lt_length_of_mem huLQ⟩
  let kuH : Fin Q.support.length :=
    ⟨Q.support.idxOf (P.getVert h), List.idxOf_lt_length_of_mem huHQ⟩
  have hgetCL : Q.support.get kcL = cL := by
    simpa [kcL] using List.getElem_idxOf
      (List.idxOf_lt_length_of_mem hcLQ)
  have hgetCH : Q.support.get kcH = cH := by
    simpa [kcH] using List.getElem_idxOf
      (List.idxOf_lt_length_of_mem hcHQ)
  have hgetUL : Q.support.get kuL = P.getVert l := by
    simpa [kuL] using List.getElem_idxOf
      (List.idxOf_lt_length_of_mem huLQ)
  have hgetUH : Q.support.get kuH = P.getVert h := by
    simpa [kuH] using List.getElem_idxOf
      (List.idxOf_lt_length_of_mem huHQ)
  have hkcLC : Q.support.get kcL ∈ offCorridorComponentFinset C := by
    rw [hgetCL]
    exact hcLC
  have hkcHC : Q.support.get kcH ∈ offCorridorComponentFinset C := by
    rw [hgetCH]
    exact hcHC
  have hcLTail :=
    component_vertex_lies_in_extreme_tail_of_qexc_eq_zero
      hP hQ htwo hnonbridge C hqexc kcL hkcLC
  have hcHTail :=
    component_vertex_lies_in_extreme_tail_of_qexc_eq_zero
      hP hQ htwo hnonbridge C hqexc kcH hkcHC

  have hkuLP : Q.support.get kuL ∈ P.support := by
    rw [hgetUL]
    exact huLP
  have hkuHP : Q.support.get kuH ∈ P.support := by
    rw [hgetUH]
    exact huHP
  obtain ⟨jL, hjL⟩ :=
    hQ.exists_corridorVisitEmbedding_eq_of_mem_P P kuL hkuLP
  obtain ⟨jH, hjH⟩ :=
    hQ.exists_corridorVisitEmbedding_eq_of_mem_P P kuH hkuHP
  let firstVisit : Fin (corridorVisitVertices P Q).length := ⟨0, by
    rw [hQ.length_corridorVisitVertices_eq_card_commonVertices]
    omega⟩
  let lastVisit : Fin (corridorVisitVertices P Q).length :=
    ⟨(corridorVisitVertices P Q).length - 1, by
      rw [hQ.length_corridorVisitVertices_eq_card_commonVertices]
      omega⟩
  let first := corridorVisitEmbedding P Q firstVisit
  let last := corridorVisitEmbedding P Q lastVisit
  change kcL < first ∨ last < kcL at hcLTail
  change kcH < first ∨ last < kcH at hcHTail
  have hfirstLast : (first : ℕ) ≤ last := by
    apply (corridorVisitEmbedding P Q).monotone
    apply Fin.mk_le_mk.mpr
    dsimp [firstVisit, lastVisit]
    omega
  have hfirstLeUL : (first : ℕ) ≤ kuL := by
    have hj : firstVisit ≤ jL := by
      apply Fin.mk_le_mk.mpr
      dsimp [firstVisit]
      omega
    have := (corridorVisitEmbedding P Q).monotone hj
    rw [hjL] at this
    exact this
  have hULLeLast : (kuL : ℕ) ≤ last := by
    have hj : jL ≤ lastVisit := by
      apply Fin.mk_le_mk.mpr
      dsimp [lastVisit]
      omega
    have := (corridorVisitEmbedding P Q).monotone hj
    rw [hjL] at this
    exact this
  have hfirstLeUH : (first : ℕ) ≤ kuH := by
    have hj : firstVisit ≤ jH := by
      apply Fin.mk_le_mk.mpr
      dsimp [firstVisit]
      omega
    have := (corridorVisitEmbedding P Q).monotone hj
    rw [hjH] at this
    exact this
  have hUHLeLast : (kuH : ℕ) ≤ last := by
    have hj : jH ≤ lastVisit := by
      apply Fin.mk_le_mk.mpr
      dsimp [lastVisit]
      omega
    have := (corridorVisitEmbedding P Q).monotone hj
    rw [hjH] at this
    exact this

  have hdistCLU : Nat.dist (kcL : ℕ) kuL = 1 := by
    have hdist := hQ.dist_eq_natDist_support_idxOf hcLQ huLQ
    rw [dist_eq_one_iff_adj.mpr hcLAdj] at hdist
    simpa [kcL, kuL] using hdist.symm
  have hdistCHU : Nat.dist (kcH : ℕ) kuH = 1 := by
    have hdist := hQ.dist_eq_natDist_support_idxOf hcHQ huHQ
    rw [dist_eq_one_iff_adj.mpr hcHAdj] at hdist
    simpa [kcH, kuH] using hdist.symm
  have hlocL :
      ((kuL : ℕ) = first ∧ (kcL : ℕ) + 1 = first) ∨
        ((kuL : ℕ) = last ∧ (kuL : ℕ) + 1 = kcL) := by
    rcases hcLTail with hinit | hfinal
    · left
      have hd := hdistCLU
      rw [Nat.dist_eq_sub_of_le (by omega)] at hd
      exact ⟨by omega, by omega⟩
    · right
      have hd := hdistCLU
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (by omega)] at hd
      exact ⟨by omega, by omega⟩
  have hlocH :
      ((kuH : ℕ) = first ∧ (kcH : ℕ) + 1 = first) ∨
        ((kuH : ℕ) = last ∧ (kuH : ℕ) + 1 = kcH) := by
    rcases hcHTail with hinit | hfinal
    · left
      have hd := hdistCHU
      rw [Nat.dist_eq_sub_of_le (by omega)] at hd
      exact ⟨by omega, by omega⟩
    · right
      have hd := hdistCHU
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (by omega)] at hd
      exact ⟨by omega, by omega⟩

  have hcommonDist := common_index_dist_eq hP hQ
    huLP huLQ huHP huHQ
  rw [hP.support_idxOf_getVert hlLen,
    hP.support_idxOf_getVert hhLen,
    Nat.dist_eq_sub_of_le hlh, ← hspanLH, hspanEq] at hcommonDist
  have hdistUU : Nat.dist (kuL : ℕ) kuH = qC + 1 := by
    simpa [kuL, kuH] using hcommonDist.symm
  have hdistCC : Nat.dist (kcL : ℕ) kcH + 1 ≤ qC := by
    have hdist := offCorridorComponent_dist_add_one_le_card C hcLC hcHC
    rw [hQ.dist_eq_natDist_support_idxOf hcLQ hcHQ] at hdist
    simpa [kcL, kcH, hcardC] using hdist
  rcases hlocL with hLi | hLf <;> rcases hlocH with hHi | hHf
  · have hd := hdistUU
    rw [hLi.1, hHi.1] at hd
    simp at hd
  · have hdUU := hdistUU
    have hleUU : (kuL : ℕ) ≤ kuH := by omega
    rw [Nat.dist_eq_sub_of_le hleUU] at hdUU
    have hdCC := hdistCC
    have hleCC : (kcL : ℕ) ≤ kcH := by omega
    rw [Nat.dist_eq_sub_of_le hleCC] at hdCC
    omega
  · have hdUU := hdistUU
    have hleUU : (kuH : ℕ) ≤ kuL := by omega
    rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hleUU] at hdUU
    have hdCC := hdistCC
    have hleCC : (kcH : ℕ) ≤ kcL := by omega
    rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hleCC] at hdCC
    omega
  · have hd := hdistUU
    rw [hLf.1, hHf.1] at hd
    simp at hd

/-- The exceptional-tail bound gives exactly the disjunction required by
`OffCorridorLocalCharge.dispatch`. -/
theorem canonical_component_dispatch_of_exceptionalTailBound
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (hnonbridge : ∀ {a b : V}, s(a, b) ∈ P.edges →
      s(a, b) ∈ Q.edges → ¬G.IsBridge s(a, b))
    (hexceptional : CanonicalExceptionalTailBound hP hQ hnonbridge)
    (C : OffCorridorComponent P) :
    canonicalAssignedQExcCount hP hQ hnonbridge C +
          offCorridorComponentRCount Q C ≥ 1 ∨
      (canonicalAssignedQExcCount hP hQ hnonbridge C = 0 ∧
        offCorridorComponentRCount Q C = 0 ∧
        canonicalAssignedExcursionCount hP hQ hnonbridge C = 0 ∧
        assignedRiddenCount (canonicalRiddenOwner hP hnonbridge) C ≤
          offCorridorComponentQCount Q C) := by
  by_cases hpos : 1 ≤ canonicalAssignedQExcCount hP hQ hnonbridge C +
      offCorridorComponentRCount Q C
  · exact Or.inl hpos
  · right
    have hq : canonicalAssignedQExcCount hP hQ hnonbridge C = 0 := by omega
    have hr : offCorridorComponentRCount Q C = 0 := by omega
    exact ⟨hq, hr,
      canonicalAssignedExcursionCount_eq_zero_of_qexc_eq_zero
        hP hQ hnonbridge C hq,
      hexceptional C hq hr⟩

/-- Fiber counting for the non-unit transition assignment. -/
theorem sum_canonicalAssignedExcursionCount
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (hnonbridge : ∀ {a b : V}, s(a, b) ∈ P.edges →
      s(a, b) ∈ Q.edges → ¬G.IsBridge s(a, b)) :
    ∑ C, canonicalAssignedExcursionCount hP hQ hnonbridge C =
      Fintype.card (ExcursionCorridorTransition P Q) := by
  classical
  calc
    ∑ C, canonicalAssignedExcursionCount hP hQ hnonbridge C =
        ∑ C : OffCorridorComponent P,
          ∑ t : ExcursionCorridorTransition P Q,
            if canonicalTransitionOwner hP hQ hnonbridge t.1 = C
            then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro C _
      let raw := canonicalAssignedExcursionTransitions hP hQ hnonbridge C
      let sub : Finset (ExcursionCorridorTransition P Q) :=
        Finset.univ.filter fun t =>
          canonicalTransitionOwner hP hQ hnonbridge t.1 = C
      have hcard : raw.card = sub.card := by
        apply Finset.card_bij (fun t ht =>
          (⟨t, (by
            have htData : corridorTransitionGap P Q t ≠ 1 ∧
                canonicalTransitionOwner hP hQ hnonbridge t = C := by
              simpa [raw, canonicalAssignedExcursionTransitions] using ht
            exact htData.1)⟩ : ExcursionCorridorTransition P Q))
        · intro t ht
          have htData : corridorTransitionGap P Q t ≠ 1 ∧
              canonicalTransitionOwner hP hQ hnonbridge t = C := by
            simpa [raw, canonicalAssignedExcursionTransitions] using ht
          simpa [sub] using htData.2
        · intro t _ u _ htu
          exact congrArg Subtype.val htu
        · intro u hu
          have huOwner : canonicalTransitionOwner hP hQ hnonbridge u.1 = C := by
            simpa [sub] using hu
          refine ⟨u.1, ?_, ?_⟩
          · simpa [raw, canonicalAssignedExcursionTransitions] using
              And.intro u.2 huOwner
          · apply Subtype.ext
            rfl
      calc
        canonicalAssignedExcursionCount hP hQ hnonbridge C = raw.card := rfl
        _ = sub.card := hcard
        _ = ∑ t : ExcursionCorridorTransition P Q,
            if canonicalTransitionOwner hP hQ hnonbridge t.1 = C
            then 1 else 0 := by simp [sub]
    _ = ∑ t : ExcursionCorridorTransition P Q,
        ∑ C : OffCorridorComponent P,
          if canonicalTransitionOwner hP hQ hnonbridge t.1 = C
          then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = Fintype.card (ExcursionCorridorTransition P Q) := by simp

/-- The global excursion count has exactly the ledger value. -/
theorem sum_canonicalAssignedExcursionCount_eq_common_sub_ridden
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (htwo : 2 ≤ (commonVertices P Q).card)
    (hnonbridge : ∀ {a b : V}, s(a, b) ∈ P.edges →
      s(a, b) ∈ Q.edges → ¬G.IsBridge s(a, b)) :
    ∑ C, canonicalAssignedExcursionCount hP hQ hnonbridge C =
      (commonVertices P Q).card - 1 -
        (riddenCorridorEdgeIndices P Q).card := by
  rw [sum_canonicalAssignedExcursionCount hP hQ hnonbridge,
    card_excursionCorridorTransition hP hQ htwo]

/-- Assemble the genuine canonical local record once the exceptional-tail
bound is supplied.  Every other field has been proved above. -/
noncomputable def canonicalOffCorridorLocalCharge
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (htwo : 2 ≤ (commonVertices P Q).card)
    (hnonbridge : ∀ {a b : V}, s(a, b) ∈ P.edges →
      s(a, b) ∈ Q.edges → ¬G.IsBridge s(a, b))
    (hexceptional : CanonicalExceptionalTailBound hP hQ hnonbridge)
    (C : OffCorridorComponent P) : OffCorridorLocalCharge P Q C where
  excursions := canonicalAssignedExcursionCount hP hQ hnonbridge C
  ridden := assignedRiddenCount (canonicalRiddenOwner hP hnonbridge) C
  gap := canonicalAssignedExcursionGap hP hQ hnonbridge C
  qexc := canonicalAssignedQExcCount hP hQ hnonbridge C
  qexc_eq := rfl
  excursions_le_gap :=
    canonicalAssignedExcursionCount_le_gap hP hQ hnonbridge C
  intervalPacking :=
    canonical_assignedRidden_add_excursionGap_le_span
      hP hQ htwo hnonbridge C
  dispatch := canonical_component_dispatch_of_exceptionalTailBound
    hP hQ hnonbridge hexceptional C

/-- The complete canonical decomposition, conditional only on the precise
exceptional-tail inequality isolated above. -/
noncomputable def canonicalOffCorridorChargeDecomposition
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (htwo : 2 ≤ (commonVertices P Q).card)
    (hnonbridge : ∀ {a b : V}, s(a, b) ∈ P.edges →
      s(a, b) ∈ Q.edges → ¬G.IsBridge s(a, b))
    (hexceptional : CanonicalExceptionalTailBound hP hQ hnonbridge) :
    OffCorridorChargeDecomposition P Q where
  component := canonicalOffCorridorLocalCharge
    hP hQ htwo hnonbridge hexceptional
  riddenOwner := canonicalRiddenOwner hP hnonbridge
  ridden_count := by
    intro C
    rfl
  ridden_owner_covers := canonicalRiddenOwner_covers hP hnonbridge
  common_nonempty := by omega
  excursions_sum :=
    sum_canonicalAssignedExcursionCount_eq_common_sub_ridden
      hP hQ htwo hnonbridge

/-- The universally quantified repaired exceptional initial/final-tail
statement. -/
def CanonicalExceptionalTailTheorem [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Prop :=
  ∀ {w x₀ y z : V} (P : G.Walk w x₀) (Q : G.Walk y z),
    (hP : IsGeodesic P) → (hQ : IsGeodesic Q) →
    2 ≤ (commonVertices P Q).card →
    (hnonbridge : ∀ {a b : V}, s(a, b) ∈ P.edges →
      s(a, b) ∈ Q.edges → ¬G.IsBridge s(a, b)) →
    CanonicalExceptionalTailBound hP hQ hnonbridge

/-- The repaired exceptional-tail statement holds for every finite simple
graph. -/
theorem canonicalExceptionalTailTheorem
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    CanonicalExceptionalTailTheorem G := by
  intro w x₀ y z P Q hP hQ htwo hnonbridge
  exact canonicalExceptionalTailBound hP hQ htwo hnonbridge

/-- The repaired exceptional-tail theorem is now sufficient for the
original exact kernel boundary. -/
theorem canonicalChargeTheorem_of_exceptionalTailTheorem
    [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hTail : CanonicalExceptionalTailTheorem G) :
    CanonicalChargeTheorem G := by
  intro w x₀ y z P Q hP hQ htwo hnonbridge
  exact ⟨canonicalOffCorridorChargeDecomposition hP hQ htwo hnonbridge
    (hTail P Q hP hQ htwo hnonbridge)⟩

/-- Complete canonical ride/excursion assignment for two finite geodesics. -/
theorem canonicalChargeTheorem
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    CanonicalChargeTheorem G :=
  canonicalChargeTheorem_of_exceptionalTailTheorem
    (canonicalExceptionalTailTheorem G)

end Erdos23GapGA
