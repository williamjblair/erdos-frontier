/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair, OpenAI Codex
-/
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Ends.Defs
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic

/-!
# Erdős 23, gap G-A: the symmetric two-demand geodesic interface

This file banks the exact Lean intake of the component-ledger proof in
`compute23/gate3/gap_ga_component_ledger.md`.

It contains:

* the symmetric two-demand cut condition;
* the bridge-cut contradiction for every edge common to the two geodesics;
* geodesic coordinate, monotonicity, and exact vertex-partition lemmas;
* canonical components of `G - V(P)`, exact `q_C/r_C` sums, and the
  kernel-checked attachment-span estimate `h_C-l_C ≤ |C|+1`;
* the repaired per-component charge, including the exceptional-tail
  dispatch found by the hostile audit; and
* conversions from canonical local charge records to `ComponentLedger` and
  hence to `D ≤ 2s`.

The remaining graph construction is isolated as `CanonicalChargeTheorem`:
assign ridden edges and consecutive excursions to the canonical components,
prove their disjoint packing inside the actual attachment intervals, and
discharge the repaired exceptional-tail case.  It is a proposition, not an
axiom, and is not proved here.  Thus this module still does **not** claim a
complete Lean proof of gap G-A.
-/

open scoped BigOperators

namespace Erdos23GapGA

open SimpleGraph

variable {V : Type*}

/-- A finite vertex set separates `a` and `b` when exactly one endpoint lies
in the set. -/
def Separates [DecidableEq V] (T : Finset V) (a b : V) : Prop :=
  (a ∈ T ∧ b ∉ T) ∨ (a ∉ T ∧ b ∈ T)

/-- The `0`/`1` demand contributed by a terminal pair across a cut. -/
def separationDemand [DecidableEq V] (T : Finset V) (a b : V) : ℕ :=
  if a ∈ T then (if b ∈ T then 0 else 1) else (if b ∈ T then 1 else 0)

/-- Number of graph edges leaving `T`, counted once from their endpoint in
`T`. -/
def cutSize [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (T : Finset V) : ℕ :=
  ∑ v ∈ T, (G.neighborFinset v \ T).card

/-- The side of a bridge cut containing its first displayed endpoint. -/
noncomputable def bridgeSide [Fintype V] (G : SimpleGraph V) (a b : V) :
    Finset V := by
  classical
  exact Finset.univ.filter fun x => (G.deleteEdges {s(a, b)}).Reachable a x

@[simp]
theorem mem_bridgeSide_iff [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (a b x : V) :
    x ∈ bridgeSide G a b ↔ (G.deleteEdges {s(a, b)}).Reachable a x := by
  classical
  simp [bridgeSide]

/-- The displayed endpoints of a bridge lie on opposite sides of its
canonical reachability cut. -/
theorem IsBridge.separates_bridgeSide [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    {a b : V} (h : G.IsBridge s(a, b)) : Separates (bridgeSide G a b) a b := by
  classical
  left
  constructor
  · simp
  · simpa [mem_bridgeSide_iff] using (isBridge_iff.mp h).2

/-- Every graph edge crossing the canonical side of a bridge is that bridge,
with the displayed orientation. -/
theorem eq_endpoints_of_mem_bridgeSide_adj_not_mem
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {a b v x : V}
    (hv : v ∈ bridgeSide G a b)
    (hx : x ∉ bridgeSide G a b) (hvx : G.Adj v x) : v = a ∧ x = b := by
  classical
  have hedge : s(v, x) = s(a, b) := by
    by_contra hne
    have hvReach : (G.deleteEdges {s(a, b)}).Reachable a v :=
      (mem_bridgeSide_iff G a b v).1 hv
    have hvxDel : (G.deleteEdges {s(a, b)}).Adj v x := by
      rw [deleteEdges_adj]
      exact ⟨hvx, by simpa using hne⟩
    exact hx ((mem_bridgeSide_iff G a b x).2 (hvReach.trans hvxDel.reachable))
  rcases (Sym2.eq_iff.mp hedge) with hforward | hreverse
  · exact hforward
  · have ha : a ∈ bridgeSide G a b := by simp
    exact (hx (hreverse.2 ▸ ha)).elim

/-- From a vertex on the canonical bridge side, the only neighbor outside
that side is the opposite endpoint, and this occurs only at the first bridge
endpoint. -/
theorem IsBridge.neighborFinset_sdiff_bridgeSide
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b v : V} (h : G.IsBridge s(a, b)) (hv : v ∈ bridgeSide G a b) :
    G.neighborFinset v \ bridgeSide G a b = if v = a then {b} else ∅ := by
  classical
  by_cases hva : v = a
  · subst v
    rw [if_pos rfl]
    ext x
    constructor
    · intro hx
      have hx' : G.Adj a x ∧ x ∉ bridgeSide G a b := by simpa using hx
      simpa using
        (eq_endpoints_of_mem_bridgeSide_adj_not_mem (by simp) hx'.2 hx'.1).2
    · intro hx
      have hxb : x = b := by simpa using hx
      subst x
      have hb : b ∉ bridgeSide G a b := by
        rcases IsBridge.separates_bridgeSide h with hsep | hsep
        · exact hsep.2
        · exact (hsep.1 (by simp)).elim
      exact Finset.mem_sdiff.mpr ⟨by simpa using (isBridge_iff.mp h).1, hb⟩
  · rw [if_neg hva]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hx' : G.Adj v x ∧ x ∉ bridgeSide G a b := by simpa using hx
    exact hva
      (eq_endpoints_of_mem_bridgeSide_adj_not_mem hv hx'.2 hx'.1).1

/-- A bridge's canonical reachability cut has exactly one crossing edge. -/
theorem IsBridge.cutSize_bridgeSide_eq_one
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V} (h : G.IsBridge s(a, b)) :
    cutSize G (bridgeSide G a b) = 1 := by
  classical
  unfold cutSize
  calc
    ∑ v ∈ bridgeSide G a b,
        (G.neighborFinset v \ bridgeSide G a b).card =
        ∑ v ∈ bridgeSide G a b, if v = a then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [IsBridge.neighborFinset_sdiff_bridgeSide h hv]
      split <;> simp
    _ = 1 := by simp

/-- A trail that uses a bridge has its endpoints on opposite sides of the
bridge's canonical cut. -/
theorem IsBridge.separates_bridgeSide_of_isTrail_mem_edges
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {a b u v : V}
    (h : G.IsBridge s(a, b)) (W : G.Walk u v) (hW : W.IsTrail)
    (he : s(a, b) ∈ W.edges) : Separates (bridgeSide G a b) u v := by
  classical
  induction W with
  | nil => simp at he
  | @cons u u' v huu' P ih =>
      rw [Walk.isTrail_cons] at hW
      simp only [Walk.edges_cons, List.mem_cons] at he
      rcases he with hhead | htail
      · have havoid : s(a, b) ∉ P.edges := by simpa [hhead] using hW.2
        have htailReach :
            (G.deleteEdges {s(a, b)}).Reachable u' v :=
          (P.toDeleteEdge s(a, b) havoid).reachable
        have hmemiff : u' ∈ bridgeSide G a b ↔ v ∈ bridgeSide G a b := by
          simp only [mem_bridgeSide_iff]
          exact ⟨fun hu' => hu'.trans htailReach,
            fun hv => hv.trans htailReach.symm⟩
        have hbnot : b ∉ bridgeSide G a b := by
          simpa [mem_bridgeSide_iff] using (isBridge_iff.mp h).2
        rcases Sym2.eq_iff.mp hhead with hforward | hreverse
        · rcases hforward with ⟨rfl, rfl⟩
          left
          exact ⟨by simp, fun hv => hbnot (hmemiff.2 hv)⟩
        · rcases hreverse with ⟨rfl, rfl⟩
          right
          exact ⟨hbnot, hmemiff.1 (by simp)⟩
      · have hne : s(u, u') ≠ s(a, b) := by
          intro heq
          exact hW.2 (heq ▸ htail)
        have hheadDel : (G.deleteEdges {s(a, b)}).Adj u u' := by
          rw [deleteEdges_adj]
          exact ⟨huu', by simpa using hne⟩
        have hmemiff : u ∈ bridgeSide G a b ↔ u' ∈ bridgeSide G a b := by
          simp only [mem_bridgeSide_iff]
          exact ⟨fun hu => hu.trans hheadDel.reachable,
            fun hu' => hu'.trans hheadDel.symm.reachable⟩
        rcases ih hW.1 htail with hforward | hreverse
        · left
          exact ⟨hmemiff.2 hforward.1, hforward.2⟩
        · right
          exact ⟨fun hu => hreverse.1 (hmemiff.1 hu), hreverse.2⟩

/-- The exact symmetric two-demand cut condition `(C)` from the component
ledger. -/
def TwoDemandCutCondition [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (w x₀ y z : V) : Prop :=
  ∀ T : Finset V,
    separationDemand T w x₀ + separationDemand T y z ≤ cutSize G T

@[simp]
theorem separates_comm [DecidableEq V] (T : Finset V) (a b : V) :
    Separates T a b ↔ Separates T b a := by
  simp only [Separates]
  tauto

@[simp]
theorem separationDemand_comm [DecidableEq V] (T : Finset V) (a b : V) :
    separationDemand T a b = separationDemand T b a := by
  by_cases ha : a ∈ T <;> by_cases hb : b ∈ T <;> simp [separationDemand, ha, hb]

@[simp]
theorem separationDemand_eq_one_iff [DecidableEq V] (T : Finset V) (a b : V) :
    separationDemand T a b = 1 ↔ Separates T a b := by
  by_cases ha : a ∈ T <;> by_cases hb : b ∈ T <;>
    simp [separationDemand, Separates, ha, hb]

/-- Under the two-demand condition, no cut of size at most one can separate
both terminal pairs.  This is the numerical contradiction used once a common
edge has been turned into a one-edge bridge cut. -/
theorem TwoDemandCutCondition.not_both_separated_by_unit_cut
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {w x₀ y z : V} (hcut : TwoDemandCutCondition G w x₀ y z)
    (T : Finset V) (hwx : Separates T w x₀) (hyz : Separates T y z)
    (hsize : cutSize G T ≤ 1) : False := by
  have hwx' : separationDemand T w x₀ = 1 :=
    (separationDemand_eq_one_iff T w x₀).2 hwx
  have hyz' : separationDemand T y z = 1 :=
    (separationDemand_eq_one_iff T y z).2 hyz
  have := hcut T
  omega

theorem TwoDemandCutCondition.swapPairs [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {w x₀ y z : V}
    (h : TwoDemandCutCondition G w x₀ y z) :
    TwoDemandCutCondition G y z w x₀ := by
  intro T
  simpa only [Nat.add_comm] using h T

theorem TwoDemandCutCondition.swapFirst [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {w x₀ y z : V}
    (h : TwoDemandCutCondition G w x₀ y z) :
    TwoDemandCutCondition G x₀ w y z := by
  intro T
  simpa only [separationDemand_comm] using h T

theorem TwoDemandCutCondition.swapSecond [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {w x₀ y z : V}
    (h : TwoDemandCutCondition G w x₀ y z) :
    TwoDemandCutCondition G w x₀ z y := by
  intro T
  simpa only [separationDemand_comm] using h T

/-- A walk is geodesic when its length realizes the graph distance between
its endpoints. -/
def IsGeodesic {G : SimpleGraph V} {u v : V} (P : G.Walk u v) : Prop :=
  P.length = G.dist u v

theorem IsGeodesic.isPath {G : SimpleGraph V} {u v : V} {P : G.Walk u v}
    (hP : IsGeodesic P) : P.IsPath :=
  P.isPath_of_length_eq_dist hP

/-- Under the two-demand condition, an edge common to the two geodesics
cannot be a bridge: its canonical bridge cut would have size one while
separating both terminal pairs. -/
theorem TwoDemandCutCondition.common_edge_not_isBridge
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {w x₀ y z a b : V} (hcut : TwoDemandCutCondition G w x₀ y z)
    {P : G.Walk w x₀} {Q : G.Walk y z} (hP : IsGeodesic P)
    (hQ : IsGeodesic Q) (heP : s(a, b) ∈ P.edges)
    (heQ : s(a, b) ∈ Q.edges) : ¬G.IsBridge s(a, b) := by
  intro hbridge
  exact hcut.not_both_separated_by_unit_cut G (bridgeSide G a b)
    (IsBridge.separates_bridgeSide_of_isTrail_mem_edges hbridge P
      hP.isPath.isTrail heP)
    (IsBridge.separates_bridgeSide_of_isTrail_mem_edges hbridge Q
      hQ.isPath.isTrail heQ)
    (by rw [IsBridge.cutSize_bridgeSide_eq_one hbridge])

/-- Every contiguous subwalk of a geodesic is geodesic.  This is the mathlib
fact used repeatedly for corridor subpaths and excursions. -/
theorem IsGeodesic.of_isSubwalk {G : SimpleGraph V} {u v u' v' : V}
    {P : G.Walk u v} {Q : G.Walk u' v'} (hP : IsGeodesic P)
    (hQP : Q.IsSubwalk P) : IsGeodesic Q := by
  exact length_eq_dist_of_subwalk hP hQP

theorem IsGeodesic.length_lt_card [Fintype V] {G : SimpleGraph V} {u v : V}
    {P : G.Walk u v} (hP : IsGeodesic P) : P.length < Fintype.card V :=
  hP.isPath.length_lt

/-- Corridor coordinates realize distance along a geodesic. -/
theorem IsGeodesic.dist_getVert_eq_sub {G : SimpleGraph V} {u v : V}
    {P : G.Walk u v} (hP : IsGeodesic P) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ P.length) : G.dist (P.getVert i) (P.getVert j) = j - i := by
  have hend : (P.drop i).getVert (j - i) = P.getVert j := by
    rw [Walk.drop_getVert]
    congr 1
    omega
  let S : G.Walk (P.getVert i) (P.getVert j) :=
    ((P.drop i).take (j - i)).copy rfl hend
  have hlength : S.length = j - i := by
    simp only [S, Walk.length_copy, Walk.take_length, Walk.drop_length]
    rw [Nat.min_eq_left]
    omega
  have hsub0 : ((P.drop i).take (j - i)).IsSubwalk P :=
    (Walk.isSubwalk_take (P.drop i) (j - i)).trans (Walk.isSubwalk_drop P i)
  have hsub : S.IsSubwalk P := hsub0.copy rfl hend rfl rfl
  calc
    G.dist (P.getVert i) (P.getVert j) = S.length := (hP.of_isSubwalk hsub).symm
    _ = j - i := hlength

/-- The basic component-span estimate.  Any path through a `t`-vertex set
joining attachments at corridor coordinates `l ≤ h` forces `h-l ≤ t+1`.

This formulation takes the internal component path explicitly; a connected
component supplies such a path. -/
theorem IsGeodesic.attachment_span_le_card_add_one [DecidableEq V]
    {G : SimpleGraph V} {u v cL cH : V} {P : G.Walk u v}
    (hP : IsGeodesic P) {l h : ℕ} (hlh : l ≤ h) (hh : h ≤ P.length)
    (C : Finset V) (hL : G.Adj cL (P.getVert l))
    (hH : G.Adj cH (P.getVert h)) (W : G.Walk cL cH) (hW : W.IsPath)
    (hWC : ∀ x ∈ W.support, x ∈ C) : h - l ≤ C.card + 1 := by
  have hsupport : W.support.toFinset ⊆ C := by
    intro x hx
    exact hWC x (by simpa using hx)
  have hWcard : W.length + 1 ≤ C.card := by
    rw [← Walk.length_support, ← List.toFinset_card_of_nodup hW.support_nodup]
    exact Finset.card_le_card hsupport
  let A : G.Walk (P.getVert l) (P.getVert h) :=
    (hL.symm.toWalk.append W).append hH.toWalk
  have hdist : G.dist (P.getVert l) (P.getVert h) ≤ W.length + 2 := by
    have := dist_le A
    simpa [A] using this
  rw [hP.dist_getVert_eq_sub hlh hh] at hdist
  omega

/-- Connectedness of the off-corridor vertex set supplies the internal path
required by `attachment_span_le_card_add_one`. -/
theorem IsGeodesic.attachment_span_le_card_add_one_of_connected
    [DecidableEq V] {G : SimpleGraph V} {u v cL cH : V} {P : G.Walk u v}
    (hP : IsGeodesic P) {l h : ℕ} (hlh : l ≤ h) (hh : h ≤ P.length)
    (C : Finset V) (hC : (G.induce (C : Set V)).Connected)
    (hcL : cL ∈ C) (hcH : cH ∈ C) (hL : G.Adj cL (P.getVert l))
    (hH : G.Adj cH (P.getVert h)) : h - l ≤ C.card + 1 := by
  obtain ⟨W, hW⟩ := hC.exists_isPath ⟨cL, hcL⟩ ⟨cH, hcH⟩
  let W' : G.Walk cL cH := W.map (Embedding.induce (C : Set V)).toHom
  have hW' : W'.IsPath := Walk.map_isPath_of_injective Subtype.val_injective hW
  have hW'C : ∀ x ∈ W'.support, x ∈ C := by
    intro x hx
    change x ∈ (W.map (Embedding.induce (C : Set V)).toHom).support at hx
    rw [Walk.support_map] at hx
    obtain ⟨x', _, hval⟩ := List.mem_map.mp hx
    rw [← hval]
    exact x'.prop
  exact hP.attachment_span_le_card_add_one hlh hh C hL hH W' hW' hW'C

/-- The vertices of a walk as a finite set. -/
def supportFinset [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (P : G.Walk u v) : Finset V :=
  P.support.toFinset

@[simp]
theorem mem_supportFinset [DecidableEq V] {G : SimpleGraph V} {u v x : V}
    (P : G.Walk u v) : x ∈ supportFinset P ↔ x ∈ P.support := by
  simp [supportFinset]

theorem IsGeodesic.card_supportFinset [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {u v : V} {P : G.Walk u v} (hP : IsGeodesic P) :
    (supportFinset P).card = P.length + 1 := by
  unfold supportFinset
  rw [List.toFinset_card_of_nodup hP.isPath.support_nodup, Walk.length_support]

theorem support_idxOf_le_length [DecidableEq V] {G : SimpleGraph V} {u v x : V}
    (P : G.Walk u v) (hx : x ∈ P.support) : P.support.idxOf x ≤ P.length := by
  have := List.idxOf_lt_length_of_mem hx
  rw [Walk.length_support] at this
  omega

/-- Two list elements whose first-occurrence indices are consecutive form a
contiguous pair in the list. -/
theorem pair_isInfix_of_idxOf_add_one [DecidableEq V] {l : List V} {x y : V}
    (hx : x ∈ l) (hy : y ∈ l) (hidx : l.idxOf y = l.idxOf x + 1) :
    [x, y] <:+: l := by
  apply List.infix_iff_getElem?.2
  refine ⟨l.idxOf x, ?_, ?_⟩
  · have hxlt := List.idxOf_lt_length_of_mem hx
    have hylt := List.idxOf_lt_length_of_mem hy
    simp only [List.length_cons, List.length_nil]
    omega
  · intro i hi
    have hi' : i = 0 ∨ i = 1 := by simp at hi; omega
    rcases hi' with rfl | rfl
    · simpa using List.getElem?_idxOf hx
    · simpa [hidx, Nat.add_comm] using List.getElem?_idxOf hy

/-- Distances between vertices of a geodesic are ordinary distances between
their corridor indices. -/
theorem IsGeodesic.dist_eq_natDist_support_idxOf [DecidableEq V]
    {G : SimpleGraph V} {u v x y : V} {P : G.Walk u v} (hP : IsGeodesic P)
    (hx : x ∈ P.support) (hy : y ∈ P.support) :
    G.dist x y = Nat.dist (P.support.idxOf x) (P.support.idxOf y) := by
  have hxv := P.getVert_support_idxOf hx
  have hyv := P.getVert_support_idxOf hy
  rcases le_total (P.support.idxOf x) (P.support.idxOf y) with hxy | hyx
  · calc
      G.dist x y =
          G.dist (P.getVert (P.support.idxOf x))
            (P.getVert (P.support.idxOf y)) := by rw [hxv, hyv]
      _ = P.support.idxOf y - P.support.idxOf x :=
        hP.dist_getVert_eq_sub hxy (support_idxOf_le_length P hy)
      _ = Nat.dist (P.support.idxOf x) (P.support.idxOf y) :=
        (Nat.dist_eq_sub_of_le hxy).symm
  · calc
      G.dist x y = G.dist y x := SimpleGraph.dist_comm
      _ = G.dist (P.getVert (P.support.idxOf y))
            (P.getVert (P.support.idxOf x)) := by rw [hxv, hyv]
      _ = P.support.idxOf x - P.support.idxOf y :=
        hP.dist_getVert_eq_sub hyx (support_idxOf_le_length P hx)
      _ = Nat.dist (P.support.idxOf x) (P.support.idxOf y) :=
        (Nat.dist_eq_sub_of_le_right hyx).symm

/-- Adjacent vertices that both lie on a geodesic are consecutive on that
geodesic, hence their edge occurs in its edge list. -/
theorem IsGeodesic.mem_edges_of_adj_of_mem_support [DecidableEq V]
    {G : SimpleGraph V} {u v x y : V} {P : G.Walk u v}
    (hP : IsGeodesic P) (hxy : G.Adj x y)
    (hx : x ∈ P.support) (hy : y ∈ P.support) : s(x, y) ∈ P.edges := by
  have hdist : Nat.dist (P.support.idxOf x) (P.support.idxOf y) = 1 := by
    rw [← hP.dist_eq_natDist_support_idxOf hx hy]
    exact dist_eq_one_iff_adj.mpr hxy
  have hsucc : P.support.idxOf y = P.support.idxOf x + 1 ∨
      P.support.idxOf x = P.support.idxOf y + 1 := by
    unfold Nat.dist at hdist
    omega
  apply (Walk.infix_support_iff_mem_edges (p := P)).1
  rcases hsucc with hsucc | hsucc
  · exact Or.inl (pair_isInfix_of_idxOf_add_one hx hy hsucc)
  · exact Or.inr (pair_isInfix_of_idxOf_add_one hy hx hsucc)

/-- On the common vertices of two geodesics, their two path-coordinate
systems induce the same pairwise distances. -/
theorem common_index_dist_eq [DecidableEq V]
    {G : SimpleGraph V} {w x₀ y z x x' : V}
    {P : G.Walk w x₀} {Q : G.Walk y z} (hP : IsGeodesic P)
    (hQ : IsGeodesic Q) (hxP : x ∈ P.support) (hxQ : x ∈ Q.support)
    (hx'P : x' ∈ P.support) (hx'Q : x' ∈ Q.support) :
    Nat.dist (P.support.idxOf x) (P.support.idxOf x') =
      Nat.dist (Q.support.idxOf x) (Q.support.idxOf x') := by
  calc
    Nat.dist (P.support.idxOf x) (P.support.idxOf x') = G.dist x x' :=
      (hP.dist_eq_natDist_support_idxOf hxP hx'P).symm
    _ = Nat.dist (Q.support.idxOf x) (Q.support.idxOf x') :=
      hQ.dist_eq_natDist_support_idxOf hxQ hx'Q

/-- Equality in the natural-number triangle inequality is exactly
betweenness. -/
theorem natDist_triangle_eq_iff_between (a b c : ℕ) :
    Nat.dist a c = Nat.dist a b + Nat.dist b c ↔
      (a ≤ b ∧ b ≤ c) ∨ (c ≤ b ∧ b ≤ a) := by
  unfold Nat.dist
  omega

/-- If three common vertices occur in this order on `Q`, their corridor
coordinates on `P` satisfy equality in the triangle inequality.  This is
the exact monotonicity invariant used by the excursion decomposition. -/
theorem corridor_index_triangle_eq_of_Q_order [DecidableEq V]
    {G : SimpleGraph V} {w x₀ y z x₁ x₂ x₃ : V}
    {P : G.Walk w x₀} {Q : G.Walk y z} (hP : IsGeodesic P)
    (hQ : IsGeodesic Q)
    (hx₁P : x₁ ∈ P.support) (hx₁Q : x₁ ∈ Q.support)
    (hx₂P : x₂ ∈ P.support) (hx₂Q : x₂ ∈ Q.support)
    (hx₃P : x₃ ∈ P.support) (hx₃Q : x₃ ∈ Q.support)
    (h₁₂ : Q.support.idxOf x₁ ≤ Q.support.idxOf x₂)
    (h₂₃ : Q.support.idxOf x₂ ≤ Q.support.idxOf x₃) :
    Nat.dist (P.support.idxOf x₁) (P.support.idxOf x₃) =
      Nat.dist (P.support.idxOf x₁) (P.support.idxOf x₂) +
        Nat.dist (P.support.idxOf x₂) (P.support.idxOf x₃) := by
  calc
    Nat.dist (P.support.idxOf x₁) (P.support.idxOf x₃) =
        Nat.dist (Q.support.idxOf x₁) (Q.support.idxOf x₃) :=
      common_index_dist_eq hP hQ hx₁P hx₁Q hx₃P hx₃Q
    _ = Nat.dist (Q.support.idxOf x₁) (Q.support.idxOf x₂) +
        Nat.dist (Q.support.idxOf x₂) (Q.support.idxOf x₃) := by
      rw [Nat.dist_eq_sub_of_le h₁₂,
        Nat.dist_eq_sub_of_le h₂₃,
        Nat.dist_eq_sub_of_le (h₁₂.trans h₂₃)]
      omega
    _ = Nat.dist (P.support.idxOf x₁) (P.support.idxOf x₂) +
        Nat.dist (P.support.idxOf x₂) (P.support.idxOf x₃) := by
      rw [common_index_dist_eq hP hQ hx₁P hx₁Q hx₂P hx₂Q,
        common_index_dist_eq hP hQ hx₂P hx₂Q hx₃P hx₃Q]

/-- Consequently, the middle common vertex in `Q`-order lies between the
outer two in corridor order. -/
theorem corridor_index_between_of_Q_order [DecidableEq V]
    {G : SimpleGraph V} {w x₀ y z x₁ x₂ x₃ : V}
    {P : G.Walk w x₀} {Q : G.Walk y z} (hP : IsGeodesic P)
    (hQ : IsGeodesic Q)
    (hx₁P : x₁ ∈ P.support) (hx₁Q : x₁ ∈ Q.support)
    (hx₂P : x₂ ∈ P.support) (hx₂Q : x₂ ∈ Q.support)
    (hx₃P : x₃ ∈ P.support) (hx₃Q : x₃ ∈ Q.support)
    (h₁₂ : Q.support.idxOf x₁ ≤ Q.support.idxOf x₂)
    (h₂₃ : Q.support.idxOf x₂ ≤ Q.support.idxOf x₃) :
    (P.support.idxOf x₁ ≤ P.support.idxOf x₂ ∧
        P.support.idxOf x₂ ≤ P.support.idxOf x₃) ∨
      (P.support.idxOf x₃ ≤ P.support.idxOf x₂ ∧
        P.support.idxOf x₂ ≤ P.support.idxOf x₁) := by
  apply (natDist_triangle_eq_iff_between _ _ _).1
  exact corridor_index_triangle_eq_of_Q_order hP hQ
    hx₁P hx₁Q hx₂P hx₂Q hx₃P hx₃Q h₁₂ h₂₃

/-- Common vertices of two walks. -/
def commonVertices [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    (P : G.Walk w x₀) (Q : G.Walk y z) : Finset V :=
  supportFinset P ∩ supportFinset Q

/-- Vertices of `Q` outside the corridor `P`. -/
def offCorridorVertices [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    (P : G.Walk w x₀) (Q : G.Walk y z) : Finset V :=
  supportFinset Q \ supportFinset P

/-- Vertices lying on neither of the two walks. -/
def unusedVertices [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {w x₀ y z : V} (P : G.Walk w x₀) (Q : G.Walk y z) : Finset V :=
  Finset.univ \ (supportFinset P ∪ supportFinset Q)

/-- The common vertices, in the order in which `Q` visits them. -/
def corridorVisitVertices [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    (P : G.Walk w x₀) (Q : G.Walk y z) : List V :=
  Q.support.filter fun x => x ∈ P.support

/-- Corridor coordinates of the common vertices, still in `Q`-order.  This
ordinary list is the index-level replacement for a dependent walk
decomposition. -/
def corridorVisitIndices [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    (P : G.Walk w x₀) (Q : G.Walk y z) : List ℕ :=
  (corridorVisitVertices P Q).map P.support.idxOf

theorem IsGeodesic.corridorVisitVertices_nodup [DecidableEq V]
    {G : SimpleGraph V} {w x₀ y z : V} {P : G.Walk w x₀} {Q : G.Walk y z}
    (hQ : IsGeodesic Q) : (corridorVisitVertices P Q).Nodup := by
  exact hQ.isPath.support_nodup.filter _

theorem IsGeodesic.length_corridorVisitVertices_eq_card_commonVertices
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z} (hQ : IsGeodesic Q) :
    (corridorVisitVertices P Q).length = (commonVertices P Q).card := by
  have hfin : (corridorVisitVertices P Q).toFinset = commonVertices P Q := by
    ext x
    simp [corridorVisitVertices, commonVertices, supportFinset, and_comm]
  rw [← hfin, List.toFinset_card_of_nodup hQ.corridorVisitVertices_nodup]

theorem IsGeodesic.corridorVisitIndices_nodup [DecidableEq V]
    {G : SimpleGraph V} {w x₀ y z : V} {P : G.Walk w x₀} {Q : G.Walk y z}
    (hQ : IsGeodesic Q) : (corridorVisitIndices P Q).Nodup := by
  unfold corridorVisitIndices
  apply hQ.corridorVisitVertices_nodup.map_on
  intro x hx y _ hxy
  apply (List.idxOf_inj (l := P.support) ?_).mp hxy
  have hx' : x ∈ Q.support ∧ x ∈ P.support := by
    simpa [corridorVisitVertices] using hx
  exact hx'.2

theorem IsGeodesic.length_corridorVisitIndices_eq_card_commonVertices
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z} (hQ : IsGeodesic Q) :
    (corridorVisitIndices P Q).length = (commonVertices P Q).card := by
  rw [corridorVisitIndices, List.length_map,
    hQ.length_corridorVisitVertices_eq_card_commonVertices]

theorem mem_corridorVisitIndices_le_length [DecidableEq V]
    {G : SimpleGraph V} {w x₀ y z : V} (P : G.Walk w x₀) (Q : G.Walk y z)
    {i : ℕ} (hi : i ∈ corridorVisitIndices P Q) : i ≤ P.length := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hi
  have hxP : x ∈ P.support := by
    have hx' : x ∈ Q.support ∧ x ∈ P.support := by
      simpa [corridorVisitVertices] using hx
    exact hx'.2
  have := List.idxOf_lt_length_of_mem hxP
  rw [Walk.length_support] at this
  omega

/-- Corridor coordinates occupied by vertices common to `P` and `Q`. -/
noncomputable def commonCorridorIndices [DecidableEq V]
    {G : SimpleGraph V} {w x₀ y z : V}
    (P : G.Walk w x₀) (Q : G.Walk y z) : Finset ℕ := by
  classical
  exact (Finset.range (P.length + 1)).filter fun i => P.getVert i ∈ Q.support

/-- Corridor-edge coordinates whose edge is ridden by `Q`. -/
noncomputable def riddenCorridorEdgeIndices [DecidableEq V]
    {G : SimpleGraph V} {w x₀ y z : V}
    (P : G.Walk w x₀) (Q : G.Walk y z) : Finset ℕ := by
  classical
  exact (Finset.range P.length).filter fun i =>
    s(P.getVert i, P.getVert (i + 1)) ∈ Q.edges

@[simp]
theorem mem_commonCorridorIndices [DecidableEq V]
    {G : SimpleGraph V} {w x₀ y z : V}
    (P : G.Walk w x₀) (Q : G.Walk y z) (i : ℕ) :
    i ∈ commonCorridorIndices P Q ↔
      i ≤ P.length ∧ P.getVert i ∈ Q.support := by
  classical
  simp [commonCorridorIndices]

@[simp]
theorem mem_riddenCorridorEdgeIndices [DecidableEq V]
    {G : SimpleGraph V} {w x₀ y z : V}
    (P : G.Walk w x₀) (Q : G.Walk y z) (i : ℕ) :
    i ∈ riddenCorridorEdgeIndices P Q ↔
      i < P.length ∧ s(P.getVert i, P.getVert (i + 1)) ∈ Q.edges := by
  classical
  simp [riddenCorridorEdgeIndices]

/-- A ridden corridor edge contributes both its start and successor
coordinates to the common-coordinate set. -/
theorem ridden_index_mem_common_and_succ
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    (P : G.Walk w x₀) (Q : G.Walk y z) {i : ℕ}
    (hi : i ∈ riddenCorridorEdgeIndices P Q) :
    i ∈ commonCorridorIndices P Q ∧
      i + 1 ∈ commonCorridorIndices P Q := by
  classical
  have hiData := (mem_riddenCorridorEdgeIndices P Q i).1 hi
  have hiQ : P.getVert i ∈ Q.support :=
    Q.fst_mem_support_of_mem_edges hiData.2
  have hisuccQ : P.getVert (i + 1) ∈ Q.support :=
    Q.snd_mem_support_of_mem_edges hiData.2
  constructor
  · exact (mem_commonCorridorIndices P Q i).2 ⟨by omega, hiQ⟩
  · exact (mem_commonCorridorIndices P Q (i + 1)).2 ⟨by omega, hisuccQ⟩

/-- The coordinate representation of the common vertices is cardinality
preserving. -/
theorem IsGeodesic.card_commonCorridorIndices_eq_commonVertices
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} (Q : G.Walk y z) (hP : IsGeodesic P) :
    (commonCorridorIndices P Q).card = (commonVertices P Q).card := by
  classical
  have himage : (commonCorridorIndices P Q).image P.getVert =
      commonVertices P Q := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      have hiData := (mem_commonCorridorIndices P Q i).1 hi
      simp [commonVertices, supportFinset, hiData.2]
    · intro hx
      have hxData : x ∈ P.support ∧ x ∈ Q.support := by
        simpa [commonVertices, supportFinset] using hx
      let i := P.support.idxOf x
      have hi : i ≤ P.length := support_idxOf_le_length P hxData.1
      have hget : P.getVert i = x := P.getVert_support_idxOf hxData.1
      apply Finset.mem_image.mpr
      refine ⟨i, (mem_commonCorridorIndices P Q i).2 ⟨hi, ?_⟩, hget⟩
      simpa [hget] using hxData.2
  rw [← himage]
  exact (Finset.card_image_iff.mpr fun i hi j hj hij =>
    hP.isPath.getVert_injOn
      (by simpa using (mem_commonCorridorIndices P Q i).1 hi |>.1)
      (by simpa using (mem_commonCorridorIndices P Q j).1 hj |>.1) hij).symm

/-- Ridden corridor-edge coordinates form a strict subset of the common
coordinates whenever there is at least one common vertex. -/
theorem riddenCorridorEdgeIndices_ssubset_commonCorridorIndices
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    (P : G.Walk w x₀) (Q : G.Walk y z)
    (hcommon : (commonCorridorIndices P Q).Nonempty) :
    riddenCorridorEdgeIndices P Q ⊂ commonCorridorIndices P Q := by
  classical
  have hsubset : riddenCorridorEdgeIndices P Q ⊆ commonCorridorIndices P Q :=
    fun _ hi => (ridden_index_mem_common_and_succ P Q hi).1
  apply (Finset.ssubset_iff_of_subset hsubset).2
  let m := (commonCorridorIndices P Q).max' hcommon
  refine ⟨m, (commonCorridorIndices P Q).max'_mem hcommon, ?_⟩
  intro hm
  have hsucc := (ridden_index_mem_common_and_succ P Q hm).2
  have hle := (commonCorridorIndices P Q).le_max' (m + 1) hsucc
  omega

/-- In particular the number of ridden edges is at most `t-1`, where `t`
is the number of common vertices. -/
theorem IsGeodesic.card_riddenCorridorEdgeIndices_le_commonVertices_sub_one
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} (Q : G.Walk y z) (hP : IsGeodesic P)
    (hcommon : 1 ≤ (commonVertices P Q).card) :
    (riddenCorridorEdgeIndices P Q).card ≤ (commonVertices P Q).card - 1 := by
  classical
  have hcoordCard := hP.card_commonCorridorIndices_eq_commonVertices Q
  have hcoordNonempty : (commonCorridorIndices P Q).Nonempty := by
    exact Finset.card_pos.mp (by omega)
  have hlt := Finset.card_lt_card
    (riddenCorridorEdgeIndices_ssubset_commonCorridorIndices P Q hcoordNonempty)
  omega

/-- The finite type of actual ridden corridor-edge coordinates. -/
abbrev RiddenCorridorEdgeIndex [DecidableEq V]
    {G : SimpleGraph V} {w x₀ y z : V}
    (P : G.Walk w x₀) (Q : G.Walk y z) :=
  {i : ℕ // i ∈ riddenCorridorEdgeIndices P Q}

/-- The vertex partition underlying `n = (d+1)+q+r`. -/
theorem card_eq_card_support_add_offCorridor_add_unused
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    (P : G.Walk w x₀) (Q : G.Walk y z) :
    Fintype.card V = (supportFinset P).card + (offCorridorVertices P Q).card +
      (unusedVertices P Q).card := by
  have hUnion :
      (supportFinset P ∪ supportFinset Q).card =
        (supportFinset P).card + (offCorridorVertices P Q).card := by
    unfold offCorridorVertices
    rw [← Finset.union_sdiff_self_eq_union, Finset.card_union_of_disjoint Finset.disjoint_sdiff]
  have hCompl := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (supportFinset P ∪ supportFinset Q))
  unfold unusedVertices at hCompl ⊢
  simp only [Finset.card_univ] at hCompl
  omega

/-- The vertices of `Q` split into off-corridor and common vertices. -/
theorem card_offCorridor_add_card_commonVertices
    [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    (P : G.Walk w x₀) (Q : G.Walk y z) :
    (offCorridorVertices P Q).card + (commonVertices P Q).card =
      (supportFinset Q).card := by
  unfold offCorridorVertices commonVertices
  rw [Finset.inter_comm]
  exact Finset.card_sdiff_add_card_inter _ _

/-- For a geodesic `Q`, its length is `q+t-1`, where `q` is the number of
off-corridor vertices and `t` is the number of common vertices. -/
theorem IsGeodesic.length_add_one_eq_card_offCorridor_add_card_commonVertices
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z} (hQ : IsGeodesic Q) :
    Q.length + 1 = (offCorridorVertices P Q).card +
      (commonVertices P Q).card := by
  rw [card_offCorridor_add_card_commonVertices, hQ.card_supportFinset]

theorem IsGeodesic.length_eq_card_offCorridor_add_card_commonVertices_sub_one
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z} (hQ : IsGeodesic Q) :
    Q.length = (offCorridorVertices P Q).card +
      (commonVertices P Q).card - 1 := by
  have := hQ.length_add_one_eq_card_offCorridor_add_card_commonVertices
    (P := P)
  omega

/-- Vertices outside a geodesic corridor, expressed in the same truncated
natural-number form as `s = n - 1 - d` in the paper. -/
def slack [Fintype V] {G : SimpleGraph V} {u v : V} (P : G.Walk u v) : ℕ :=
  Fintype.card V - 1 - P.length

/-- The slack outside a geodesic corridor is exactly `q+r`: vertices used by
`Q` off `P`, plus vertices used by neither walk. -/
theorem IsGeodesic.slack_eq_card_offCorridor_add_card_unused
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z} (hP : IsGeodesic P) :
    slack P = (offCorridorVertices P Q).card + (unusedVertices P Q).card := by
  have hpartition := card_eq_card_support_add_offCorridor_add_unused P Q
  have hpCard := hP.card_supportFinset
  unfold slack
  omega

/-- The support of a connected component, realized as a finset without
requiring a separate `Fintype C.supp` instance. -/
noncomputable def connectedComponentFinset {W : Type*} [Fintype W]
    {H : SimpleGraph W} (C : H.ConnectedComponent) : Finset W := by
  classical
  exact Finset.univ.filter fun x => x ∈ C.supp

@[simp]
theorem mem_connectedComponentFinset {W : Type*} [Fintype W]
    {H : SimpleGraph W} (C : H.ConnectedComponent) (x : W) :
    x ∈ connectedComponentFinset C ↔ x ∈ C.supp := by
  classical
  simp [connectedComponentFinset]

/-- Connected components partition every finite vertex subset.  This generic
double-counting lemma is the bookkeeping engine for summing the `q_C` and
`r_C` terms over the components of `B - V(P)`. -/
theorem sum_card_inter_connectedComponent_supp
    {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) (S : Finset W) :
    ∑ C : H.ConnectedComponent, (connectedComponentFinset C ∩ S).card = S.card := by
  classical
  calc
    ∑ C : H.ConnectedComponent, (connectedComponentFinset C ∩ S).card =
        ∑ C : H.ConnectedComponent, ∑ x ∈ S, if x ∈ C.supp then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro C _
      rw [Finset.sum_boole]
      congr 1
      ext x
      simp [connectedComponentFinset, and_comm]
    _ = ∑ x ∈ S, ∑ C : H.ConnectedComponent,
        if x ∈ C.supp then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = S.card := by
      simp [ConnectedComponent.mem_supp_iff]

/-- A component of the graph obtained by deleting the corridor vertices. -/
abbrev OffCorridorComponent [DecidableEq V] {G : SimpleGraph V}
    {u v : V} (P : G.Walk u v) :=
  G.ComponentCompl (supportFinset P : Set V)

/-- Number of actual ridden edges assigned to a specified canonical
off-corridor component. -/
noncomputable def assignedRiddenCount
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (owner : RiddenCorridorEdgeIndex P Q → OffCorridorComponent P)
    (C : OffCorridorComponent P) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => owner i = C).card

/-- Fiber counting: assigning every actual ridden coordinate to one component
partitions the ridden set exactly. -/
theorem sum_assignedRiddenCount
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z}
    (owner : RiddenCorridorEdgeIndex P Q → OffCorridorComponent P) :
    ∑ C, assignedRiddenCount owner C = (riddenCorridorEdgeIndices P Q).card := by
  classical
  calc
    ∑ C, assignedRiddenCount owner C =
        ∑ C : OffCorridorComponent P, ∑ i, if owner i = C then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro C _
      simp [assignedRiddenCount]
    _ = ∑ i, ∑ C : OffCorridorComponent P, if owner i = C then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ _i : RiddenCorridorEdgeIndex P Q, 1 := by simp
    _ = (riddenCorridorEdgeIndices P Q).card := by simp

/-- The vertices of an off-corridor component, as a finset in the original
vertex type. -/
noncomputable def offCorridorComponentFinset [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {u v : V} {P : G.Walk u v}
    (C : OffCorridorComponent P) : Finset V := by
  classical
  exact Finset.univ.filter fun x => x ∈ C

@[simp]
theorem mem_offCorridorComponentFinset [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {u v x : V} {P : G.Walk u v}
    (C : OffCorridorComponent P) :
    x ∈ offCorridorComponentFinset C ↔ x ∈ C := by
  classical
  simp [offCorridorComponentFinset]

/-- The complements' connected components partition every finite set after
the deleted corridor vertices are removed. -/
theorem sum_card_inter_offCorridorComponent
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (P : G.Walk u v) (S : Finset V) :
    ∑ C : OffCorridorComponent P,
        (offCorridorComponentFinset C ∩ S).card =
      (S \ supportFinset P).card := by
  classical
  calc
    ∑ C : OffCorridorComponent P,
        (offCorridorComponentFinset C ∩ S).card =
        ∑ C : OffCorridorComponent P, ∑ x ∈ S, if x ∈ C then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro C _
      rw [Finset.sum_boole]
      congr 1
      ext x
      simp [offCorridorComponentFinset, and_comm]
    _ = ∑ x ∈ S, ∑ C : OffCorridorComponent P,
        if x ∈ C then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x ∈ S, if x ∉ supportFinset P then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ supportFinset P
      · simp [ComponentCompl.mem_supp_iff, hx]
      · simp [ComponentCompl.mem_supp_iff, hx]
    _ = (S \ supportFinset P).card := by
      rw [Finset.sum_boole, ← Finset.sdiff_eq_filter]
      norm_cast

/-- Number of vertices of an off-corridor component used by `Q`. -/
noncomputable def offCorridorComponentQCount
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} (Q : G.Walk y z) (C : OffCorridorComponent P) : ℕ :=
  (offCorridorComponentFinset C ∩ supportFinset Q).card

/-- Number of vertices of an off-corridor component unused by `Q`. -/
noncomputable def offCorridorComponentRCount
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} (Q : G.Walk y z) (C : OffCorridorComponent P) : ℕ :=
  (offCorridorComponentFinset C ∩
    (Finset.univ \ supportFinset Q)).card

/-- The local `q_C` counts sum exactly to the number of `Q`-vertices off
the corridor. -/
theorem sum_offCorridorComponentQCount
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    (P : G.Walk w x₀) (Q : G.Walk y z) :
    ∑ C : OffCorridorComponent P, offCorridorComponentQCount Q C =
      (offCorridorVertices P Q).card := by
  classical
  simpa [offCorridorComponentQCount, offCorridorVertices] using
    sum_card_inter_offCorridorComponent P (supportFinset Q)

/-- The local `r_C` counts sum exactly to the number of vertices used by
neither geodesic. -/
theorem sum_offCorridorComponentRCount
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    (P : G.Walk w x₀) (Q : G.Walk y z) :
    ∑ C : OffCorridorComponent P, offCorridorComponentRCount Q C =
      (unusedVertices P Q).card := by
  classical
  rw [show (∑ C : OffCorridorComponent P, offCorridorComponentRCount Q C) =
      ((Finset.univ \ supportFinset Q) \ supportFinset P).card by
    simpa [offCorridorComponentRCount] using
      sum_card_inter_offCorridorComponent P (Finset.univ \ supportFinset Q)]
  congr 1
  ext x
  simp [unusedVertices, and_comm]

/-- Inside one canonical component, its vertices split exactly into those
used by `Q` and those used by neither path. -/
theorem offCorridorComponentQCount_add_RCount
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} (Q : G.Walk y z) (C : OffCorridorComponent P) :
    offCorridorComponentQCount Q C + offCorridorComponentRCount Q C =
      (offCorridorComponentFinset C).card := by
  classical
  have hcomp :
      offCorridorComponentFinset C ∩ (Finset.univ \ supportFinset Q) =
        offCorridorComponentFinset C \ supportFinset Q := by
    ext x
    simp
  rw [offCorridorComponentQCount, offCorridorComponentRCount, hcomp]
  have hpartition := Finset.card_sdiff_add_card_inter
    (offCorridorComponentFinset C) (supportFinset Q)
  omega

/-- Corridor coordinates adjacent to a fixed component of `B - V(P)`. -/
noncomputable def offCorridorAttachmentIndices
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (P : G.Walk u v) (C : OffCorridorComponent P) : Finset ℕ := by
  classical
  exact (Finset.range (P.length + 1)).filter fun i =>
    ∃ c ∈ offCorridorComponentFinset C, G.Adj c (P.getVert i)

/-- The attachment interval length `h_C-l_C`, with value zero for a
component not attached to the corridor. -/
noncomputable def offCorridorComponentSpan
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (P : G.Walk u v) (C : OffCorridorComponent P) : ℕ := by
  classical
  let A := offCorridorAttachmentIndices P C
  exact if hA : A.Nonempty then A.max' hA - A.min' hA else 0

/-- A component's attachment interval crosses the corridor edge with start
coordinate `i`.  This is the concrete witness required of every ridden-edge
owner in the canonical charge certificate. -/
def offCorridorComponentCoversIndex
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (P : G.Walk u v) (C : OffCorridorComponent P) (i : ℕ) : Prop :=
  ∃ l ∈ offCorridorAttachmentIndices P C,
    ∃ h ∈ offCorridorAttachmentIndices P C, l ≤ i ∧ i + 1 ≤ h

@[simp]
theorem mem_offCorridorAttachmentIndices
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (P : G.Walk u v) (C : OffCorridorComponent P) (i : ℕ) :
    i ∈ offCorridorAttachmentIndices P C ↔
      i ≤ P.length ∧
        ∃ c ∈ offCorridorComponentFinset C, G.Adj c (P.getVert i) := by
  classical
  simp [offCorridorAttachmentIndices]

/-- A component's attachment interval has length at most its number of
vertices plus one.  This is inequality `(1)` of the paper proof, now for the
canonical components of `B - V(P)`. -/
theorem IsGeodesic.offCorridorComponentSpan_le_card_add_one
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v : V}
    {P : G.Walk u v} (hP : IsGeodesic P) (C : OffCorridorComponent P) :
    offCorridorComponentSpan P C ≤
      (offCorridorComponentFinset C).card + 1 := by
  classical
  let A := offCorridorAttachmentIndices P C
  by_cases hA : A.Nonempty
  · let l := A.min' hA
    let h := A.max' hA
    have hlmem : l ∈ A := A.min'_mem hA
    have hhmem : h ∈ A := A.max'_mem hA
    have hlh : l ≤ h := A.min'_le_max' hA
    have hlData := (mem_offCorridorAttachmentIndices P C l).1 hlmem
    have hhData := (mem_offCorridorAttachmentIndices P C h).1 hhmem
    obtain ⟨cL, hcLC, hcLAdj⟩ := hlData.2
    obtain ⟨cH, hcHC, hcHAdj⟩ := hhData.2
    have hcLmem : cL ∈ C :=
      (mem_offCorridorComponentFinset C (x := cL)).1 hcLC
    have hcHmem : cH ∈ C :=
      (mem_offCorridorComponentFinset C (x := cH)).1 hcHC
    obtain ⟨hcLoff, hcLeq⟩ :=
      (ComponentCompl.mem_supp_iff.mp hcLmem)
    obtain ⟨hcHoff, hcHeq⟩ :=
      (ComponentCompl.mem_supp_iff.mp hcHmem)
    let cL' : {x : V // x ∉ (supportFinset P : Set V)} := ⟨cL, hcLoff⟩
    let cH' : {x : V // x ∉ (supportFinset P : Set V)} := ⟨cH, hcHoff⟩
    have hcL' : cL' ∈ ConnectedComponent.supp C :=
      (ConnectedComponent.mem_supp_iff C cL').2 hcLeq
    have hcH' : cH' ∈ ConnectedComponent.supp C :=
      (ConnectedComponent.mem_supp_iff C cH').2 hcHeq
    obtain ⟨W, hW⟩ := C.connected_toSimpleGraph.exists_isPath ⟨cL', hcL'⟩ ⟨cH', hcH'⟩
    let Woff := W.map C.toSimpleGraph_hom
    let W' : G.Walk cL cH :=
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
    have hspan := hP.attachment_span_le_card_add_one hlh hhData.1
      (offCorridorComponentFinset C) hcLAdj hcHAdj W' hW' hW'C
    simpa [offCorridorComponentSpan, A, hA, l, h] using hspan
  · simp [offCorridorComponentSpan, A, hA]

/-- If two geodesics have at most one common vertex, the desired estimate is
pure vertex counting; no cut condition is needed. -/
theorem length_le_slack_of_commonVertices_card_le_one
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z} (hP : IsGeodesic P)
    (hQ : IsGeodesic Q) (hcommon : (commonVertices P Q).card ≤ 1) :
    Q.length ≤ slack P := by
  have hpCard := hP.card_supportFinset
  have hqCard := hQ.card_supportFinset
  have hinclusion := Finset.card_union_add_card_inter (supportFinset P) (supportFinset Q)
  have hunion : (supportFinset P ∪ supportFinset Q).card ≤ Fintype.card V := by
    simpa using Finset.card_le_card (Finset.subset_univ (supportFinset P ∪ supportFinset Q))
  unfold commonVertices at hcommon
  unfold slack
  omega

/-- The final numerical ledger extracted from the component decomposition.

`q` is the number of `Q`-vertices off `P`, `r` is the number of vertices off
both paths, `excursions` is `E`, and `ridden` is `|R|`. -/
structure ComponentLedger [Fintype V] {G : SimpleGraph V}
    {w x₀ y z : V} (P : G.Walk w x₀) (Q : G.Walk y z) where
  q : ℕ
  r : ℕ
  excursions : ℕ
  ridden : ℕ
  card_decomposition : Fintype.card V = P.length + 1 + q + r
  length_decomposition : Q.length = q + excursions + ridden
  charge : ridden + excursions ≤ q + 2 * r

/-- The numerical data attached to one component of `B - V(P)` in the
paper proof.  The fields deliberately retain the interval length `gap` and
the number `qexc` of internal excursion vertices: this makes the local
charge a consequence of the component-span estimate, rather than a renamed
copy of the desired global inequality.

The exceptional alternative is exactly the repaired initial/final-tail
case from the hostile audit. -/
structure LocalComponentCharge where
  q : ℕ
  r : ℕ
  excursions : ℕ
  ridden : ℕ
  gap : ℕ
  qexc : ℕ
  qexc_eq : qexc = gap - excursions
  excursions_le_gap : excursions ≤ gap
  span_charge : ridden + gap ≤ q + r + 1
  dispatch : qexc + r ≥ 1 ∨ (qexc = 0 ∧ r = 0 ∧ excursions = 0 ∧ ridden ≤ q)

namespace LocalComponentCharge

/-- The exact per-component inequality `(3)`, including the exceptional
tail component repaired by the first hostile audit. -/
theorem charge (L : LocalComponentCharge) :
    L.ridden + L.excursions ≤ L.q + 2 * L.r := by
  rcases L.dispatch with hnonexceptional | hexceptional
  · have hgap : L.gap = L.qexc + L.excursions := by
      have := L.qexc_eq
      have := L.excursions_le_gap
      omega
    have hspan := L.span_charge
    omega
  · rcases hexceptional with ⟨hqexc, hr, hexc, hridden⟩
    omega

end LocalComponentCharge

/-- The genuinely graph-theoretic data for one *canonical* component of
`G - V(P)`.  The quantities `q_C` and `r_C` are no longer fields: they are
the actual cardinalities defined above.  Likewise `intervalPacking` is
measured against the actual attachment span proved bounded by `(1)`.

Constructing these records from consecutive corridor visits is the remaining
excursion-decomposition step. -/
structure OffCorridorLocalCharge [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ y z : V} (P : G.Walk w x₀)
    (Q : G.Walk y z) (C : OffCorridorComponent P) where
  excursions : ℕ
  ridden : ℕ
  gap : ℕ
  qexc : ℕ
  qexc_eq : qexc = gap - excursions
  excursions_le_gap : excursions ≤ gap
  intervalPacking : ridden + gap ≤ offCorridorComponentSpan P C
  dispatch : qexc + offCorridorComponentRCount Q C ≥ 1 ∨
    (qexc = 0 ∧ offCorridorComponentRCount Q C = 0 ∧ excursions = 0 ∧
      ridden ≤ offCorridorComponentQCount Q C)

namespace OffCorridorLocalCharge

/-- The canonical graph record implies the abstract local charge.  This
conversion uses the proved attachment-span bound and the exact `q_C/r_C`
vertex partition. -/
noncomputable def toLocalComponentCharge
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    {P : G.Walk w x₀} {Q : G.Walk y z} {C : OffCorridorComponent P}
    (D : OffCorridorLocalCharge P Q C) (hP : IsGeodesic P) :
    LocalComponentCharge where
  q := offCorridorComponentQCount Q C
  r := offCorridorComponentRCount Q C
  excursions := D.excursions
  ridden := D.ridden
  gap := D.gap
  qexc := D.qexc
  qexc_eq := D.qexc_eq
  excursions_le_gap := D.excursions_le_gap
  span_charge := by
    have hpacking := D.intervalPacking
    have hspan := hP.offCorridorComponentSpan_le_card_add_one C
    have hpartition := offCorridorComponentQCount_add_RCount Q C
    omega
  dispatch := D.dispatch

end OffCorridorLocalCharge

/-- A canonical component-by-component excursion decomposition.  Unlike the
compact `ComponentLedger`, its index type and its `q_C,r_C` values are fixed
by the graph itself, and each local record must prove the attachment-interval
packing and the exceptional-tail dispatch. -/
structure OffCorridorChargeDecomposition
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
    (P : G.Walk w x₀) (Q : G.Walk y z) where
  component : (C : OffCorridorComponent P) → OffCorridorLocalCharge P Q C
  riddenOwner : RiddenCorridorEdgeIndex P Q → OffCorridorComponent P
  ridden_count : ∀ C, (component C).ridden = assignedRiddenCount riddenOwner C
  ridden_owner_covers : ∀ i,
    offCorridorComponentCoversIndex P (riddenOwner i) i.1
  common_nonempty : 1 ≤ (commonVertices P Q).card
  excursions_sum : ∑ C, (component C).excursions =
    (commonVertices P Q).card - 1 - (riddenCorridorEdgeIndices P Q).card

/-- A finite family of local component charges, together with the four
global bookkeeping identities proved by the excursion decomposition.  In
contrast to `ComponentLedger`, every local charge still exposes the span
and exceptional-case obligations used to obtain it. -/
structure ComponentChargeFamily [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {w x₀ y z : V} (P : G.Walk w x₀) (Q : G.Walk y z) where
  ι : Type*
  [finite : Fintype ι]
  component : ι → LocalComponentCharge
  q_sum : ∑ i, (component i).q = (offCorridorVertices P Q).card
  r_sum : ∑ i, (component i).r = (unusedVertices P Q).card
  excursions_sum : ∑ i, (component i).excursions =
    (commonVertices P Q).card - 1 - ∑ i, (component i).ridden
  ridden_le_common : ∑ i, (component i).ridden ≤ (commonVertices P Q).card - 1
  common_nonempty : 1 ≤ (commonVertices P Q).card

attribute [instance] ComponentChargeFamily.finite

namespace OffCorridorChargeDecomposition

variable [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
  {P : G.Walk w x₀} {Q : G.Walk y z}

/-- The per-component ridden counts are genuine fibers of an assignment of
the actual ridden corridor coordinates. -/
theorem ridden_sum (D : OffCorridorChargeDecomposition P Q) :
    ∑ C, (D.component C).ridden = (riddenCorridorEdgeIndices P Q).card := by
  calc
    ∑ C, (D.component C).ridden =
        ∑ C, assignedRiddenCount D.riddenOwner C := by
      apply Finset.sum_congr rfl
      intro C _
      exact D.ridden_count C
    _ = (riddenCorridorEdgeIndices P Q).card :=
      sum_assignedRiddenCount D.riddenOwner

/-- Forgetting the canonical graph structure gives a finite family of the
audited local numerical charges. -/
noncomputable def toComponentChargeFamily
    (D : OffCorridorChargeDecomposition P Q) (hP : IsGeodesic P) :
    ComponentChargeFamily P Q where
  ι := OffCorridorComponent P
  finite := inferInstance
  component := fun C => (D.component C).toLocalComponentCharge hP
  q_sum := by
    simpa [OffCorridorLocalCharge.toLocalComponentCharge] using
      sum_offCorridorComponentQCount P Q
  r_sum := by
    simpa [OffCorridorLocalCharge.toLocalComponentCharge] using
      sum_offCorridorComponentRCount P Q
  excursions_sum := by
    simp only [OffCorridorLocalCharge.toLocalComponentCharge]
    rw [D.excursions_sum, D.ridden_sum]
  ridden_le_common := by
    simp only [OffCorridorLocalCharge.toLocalComponentCharge]
    rw [D.ridden_sum]
    exact hP.card_riddenCorridorEdgeIndices_le_commonVertices_sub_one Q D.common_nonempty
  common_nonempty := D.common_nonempty

end OffCorridorChargeDecomposition

namespace ComponentLedger

variable [Fintype V] {G : SimpleGraph V} {w x₀ y z : V}
  {P : G.Walk w x₀} {Q : G.Walk y z}

/-- A stronger estimate `length Q ≤ s` gives a ledger immediately.  This is
the constructor used for the zero/one-intersection cases. -/
def of_length_le_slack (hP : IsGeodesic P) (h : Q.length ≤ slack P) :
    ComponentLedger P Q where
  q := Q.length
  r := slack P - Q.length
  excursions := 0
  ridden := 0
  card_decomposition := by
    have hpCard := hP.length_lt_card
    unfold slack at h ⊢
    omega
  length_decomposition := by simp
  charge := by simp

/-- The component ledger exists unconditionally when the geodesics share at
most one vertex. -/
def of_commonVertices_card_le_one [DecidableEq V] (hP : IsGeodesic P)
    (hQ : IsGeodesic Q) (hcommon : (commonVertices P Q).card ≤ 1) :
    ComponentLedger P Q :=
  of_length_le_slack hP
    (length_le_slack_of_commonVertices_card_le_one hP hQ hcommon)

theorem slack_eq (L : ComponentLedger P Q) : slack P = L.q + L.r := by
  unfold slack
  have hcard := L.card_decomposition
  omega

/-- The final display in the component-ledger proof: `(L)` implies
`D ≤ 2s`. -/
theorem length_le_twice_slack (L : ComponentLedger P Q) :
    Q.length ≤ 2 * slack P := by
  rw [L.slack_eq]
  have hlength := L.length_decomposition
  have hcharge := L.charge
  omega

/-- Applying the ledger in both terminal-pair orders gives the second
single-edge inequality `2D ≤ 2s+d`. -/
theorem two_mul_length_le_twice_slack_add_length
    (L : ComponentLedger P Q) (Lswap : ComponentLedger Q P) :
    2 * Q.length ≤ 2 * slack P + P.length := by
  have hforwardCard := L.card_decomposition
  have hswapCard := Lswap.card_decomposition
  have hswap := Lswap.length_le_twice_slack
  unfold slack at hswap ⊢
  omega

/-- The two numerical conclusions `SE1` and `SE2`, conditional only on the
forward and swapped component ledgers. -/
theorem symmetric_bounds (L : ComponentLedger P Q) (Lswap : ComponentLedger Q P) :
    Q.length ≤ 2 * slack P ∧ 2 * Q.length ≤ 2 * slack P + P.length :=
  ⟨L.length_le_twice_slack, L.two_mul_length_le_twice_slack_add_length Lswap⟩

end ComponentLedger

namespace ComponentChargeFamily

variable [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
  {P : G.Walk w x₀} {Q : G.Walk y z}

/-- Summing the audited local component inequality gives the global charge
`|R|+E ≤ q+2r`. -/
theorem sum_charge (F : ComponentChargeFamily P Q) :
    (∑ i, (F.component i).ridden) +
        ∑ i, (F.component i).excursions ≤
      (offCorridorVertices P Q).card + 2 * (unusedVertices P Q).card := by
  letI := F.finite
  calc
    (∑ i, (F.component i).ridden) + ∑ i, (F.component i).excursions =
        ∑ i, ((F.component i).ridden + (F.component i).excursions) := by
      rw [Finset.sum_add_distrib]
    _ ≤ ∑ i, ((F.component i).q + 2 * (F.component i).r) := by
      exact Finset.sum_le_sum fun i _ => (F.component i).charge
    _ = (∑ i, (F.component i).q) + 2 * ∑ i, (F.component i).r := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = (offCorridorVertices P Q).card + 2 * (unusedVertices P Q).card := by
      rw [F.q_sum, F.r_sum]

/-- The graph-theoretic component family produces the original compact
`ComponentLedger`.  All arithmetic and all path-cardinality bookkeeping in
this conversion are kernel-checked here. -/
def toComponentLedger (F : ComponentChargeFamily P Q) (hP : IsGeodesic P)
    (hQ : IsGeodesic Q) : ComponentLedger P Q := by
  letI := F.finite
  exact
    { q := (offCorridorVertices P Q).card
      r := (unusedVertices P Q).card
      excursions := ∑ i, (F.component i).excursions
      ridden := ∑ i, (F.component i).ridden
      card_decomposition := by
        have hpartition := card_eq_card_support_add_offCorridor_add_unused P Q
        have hpCard := hP.card_supportFinset
        omega
      length_decomposition := by
        have hlength :=
          hQ.length_eq_card_offCorridor_add_card_commonVertices_sub_one (P := P)
        have hexc := F.excursions_sum
        have hridden := F.ridden_le_common
        have hcommon := F.common_nonempty
        omega
      charge := by
        exact F.sum_charge }

end ComponentChargeFamily

namespace OffCorridorChargeDecomposition

variable [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w x₀ y z : V}
  {P : G.Walk w x₀} {Q : G.Walk y z}

/-- A canonical component decomposition gives the compact component ledger. -/
noncomputable def toComponentLedger
    (D : OffCorridorChargeDecomposition P Q) (hP : IsGeodesic P)
    (hQ : IsGeodesic Q) : ComponentLedger P Q :=
  (D.toComponentChargeFamily hP).toComponentLedger hP hQ

/-- Consequently, the canonical attachment/excursion certificate proves the
pure metric bound. -/
theorem length_le_twice_slack
    (D : OffCorridorChargeDecomposition P Q) (hP : IsGeodesic P)
    (hQ : IsGeodesic Q) : Q.length ≤ 2 * slack P :=
  (D.toComponentLedger hP hQ).length_le_twice_slack

end OffCorridorChargeDecomposition

/-- Exact remaining graph-construction lemma.  It is strictly more
structured than the desired metric bound: for every canonical component of
`G - V(P)` it must construct the excursion counts, assigned ridden-edge
count, total excursion gap, and internal-excursion count, prove their packing
inside the *actual* attachment span, and discharge the audited exceptional
tail case. -/
def CanonicalChargeTheorem [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Prop :=
  ∀ {w x₀ y z : V} (P : G.Walk w x₀) (Q : G.Walk y z),
    IsGeodesic P → IsGeodesic Q → 2 ≤ (commonVertices P Q).card →
    (∀ {a b : V}, s(a, b) ∈ P.edges → s(a, b) ∈ Q.edges →
      ¬G.IsBridge s(a, b)) →
    Nonempty (OffCorridorChargeDecomposition P Q)

/-- The desired pure metric theorem follows from the exact canonical charge
construction, with the zero/one-common-vertex cases discharged separately. -/
theorem length_le_twice_slack_of_canonicalChargeTheorem
    [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hcanonical : CanonicalChargeTheorem G)
    {w x₀ y z : V} {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (hnonbridge : ∀ {a b : V}, s(a, b) ∈ P.edges →
      s(a, b) ∈ Q.edges → ¬G.IsBridge s(a, b)) :
    Q.length ≤ 2 * slack P := by
  by_cases hsmall : (commonVertices P Q).card ≤ 1
  · have hone := length_le_slack_of_commonVertices_card_le_one hP hQ hsmall
    omega
  · have htwo : 2 ≤ (commonVertices P Q).card := by omega
    exact (hcanonical P Q hP hQ htwo hnonbridge).some.length_le_twice_slack hP hQ

/-- The one remaining mathematical obligation in the proposed proof: build
the component ledger from two geodesics and the symmetric cut condition.

This is a proposition, not an axiom.  Keeping it named makes the dependency
boundary auditable without asserting that it has been proved. -/
def LedgerTheorem [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (w x₀ y z : V) : Prop :=
  ∀ (P : G.Walk w x₀) (Q : G.Walk y z),
    IsGeodesic P → IsGeodesic Q → TwoDemandCutCondition G w x₀ y z →
      Nonempty (ComponentLedger P Q)

/-- The canonical charge theorem also closes the original cut-condition
ledger interface, because the bridge-cut lemma supplies its nonbridge
hypothesis. -/
theorem ledgerTheorem_of_canonicalChargeTheorem
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcanonical : CanonicalChargeTheorem G) (w x₀ y z : V) :
    LedgerTheorem G w x₀ y z := by
  intro P Q hP hQ hcut
  by_cases hsmall : (commonVertices P Q).card ≤ 1
  · exact ⟨ComponentLedger.of_commonVertices_card_le_one hP hQ hsmall⟩
  · have htwo : 2 ≤ (commonVertices P Q).card := by omega
    obtain ⟨D⟩ := hcanonical P Q hP hQ htwo (fun heP heQ =>
      hcut.common_edge_not_isBridge G hP hQ heP heQ)
    exact ⟨D.toComponentLedger hP hQ⟩

end Erdos23GapGA
