/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair, OpenAI Codex
-/
import ErdosProblems.Erdos23GapGBTwoDemand

/-!
# Erdős 23 G-B: weighted two-demand closure

The old order-only estimate `D1+D2 <= n+p-2` is false.  This file instead
uses two inequalities which follow separately from the already-proved G-A
component ledger:

* rooted SE2: `2*Dmax <= 2*s+d`;
* internal-pair SE2: `Dmin+2*Dmax <= 2*(s+d)`.

Together they pay the full two-demand RL cost whenever `2*d < s`.  This is
a proper unconditional subregime of the strict BF-RL residual and includes
the long shared-endpoint diamond-chain counterexamples to the old estimate.
-/

namespace Erdos23GapGBTwoDemandWeighted

open scoped BigOperators
open SimpleGraph
open Erdos23GapGA
open Erdos23GapGBSeries
open Erdos23GapGBEqualityBoundary
open Erdos23GapGBTwoDemand

/-- Left endpoint of the weighted convex interval. -/
private theorem weightedLeftCorner
    {b c q L : ℕ}
    (hcEq : c + 2 * b = L) (hcq : c + q = b)
    (hqBound : 7 * q ≤ 6 * b) :
    9 * (c ^ 2 + b ^ 2) ≤ 2 * L ^ 2 := by
  let k := 6 * b - 7 * q
  have hkEq : 7 * q + k = 6 * b := by
    simp only [k]
    omega
  have hid : 2 * L ^ 2 = 9 * (c ^ 2 + b ^ 2) + q * k := by
    nlinarith
  rw [hid]
  omega

/-- Right endpoint of the weighted convex interval. -/
private theorem weightedRightCorner
    {b c r U d : ℕ}
    (hrEq : 2 * b + r = U) (hcr : r + d + 1 = c)
    (hcoefficient : 8 * c ≤ 4 * b + 5 * r) :
    4 * (c ^ 2 + b ^ 2) ≤ 4 * (d + 1) ^ 2 + U ^ 2 := by
  let k := 4 * b + 5 * r - 8 * c
  have hkEq : 8 * c + k = 4 * b + 5 * r := by
    simp only [k]
    omega
  have hid : 4 * (d + 1) ^ 2 + U ^ 2 =
      4 * (c ^ 2 + b ^ 2) + r * k := by
    nlinarith
  rw [hid]
  omega

/-- Convex landing for `a <= b`, `a+2b <= L`, and `2b <= U`, when
the equal and upper endpoint costs are both bounded by `R`. -/
private theorem weightedConvexInterval
    {a b L U d R : ℕ}
    (hab : a ≤ b) (habL : a + 2 * b ≤ L) (hbU : 2 * b ≤ U)
    (hLU : L = U + d + 1)
    (hequalEndpoint : 2 * L ^ 2 ≤ 9 * R)
    (hrootEndpoint : 4 * (d + 1) ^ 2 + U ^ 2 ≤ 4 * R) :
    a ^ 2 + b ^ 2 ≤ R := by
  by_cases hsmallB : 3 * b ≤ L
  · have haSq : a ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left hab 2
    have hbScaled : 9 * b ^ 2 ≤ L ^ 2 := by
      have hsquare := Nat.pow_le_pow_left hsmallB 2
      nlinarith
    have hscaled : 9 * (a ^ 2 + b ^ 2) ≤ 2 * L ^ 2 := by
      nlinarith
    have := hscaled.trans hequalEndpoint
    omega
  · have hlargeB : L ≤ 3 * b := by omega
    have htwoBL : 2 * b ≤ L := by omega
    let c := L - 2 * b
    let q := 3 * b - L
    let r := U - 2 * b
    have hcEq : c + 2 * b = L := by simp only [c]; omega
    have hac : a ≤ c := by omega
    have hqEq : L + q = 3 * b := by simp only [q]; omega
    have hrEq : 2 * b + r = U := by simp only [r]; omega
    have hcq : c + q = b := by omega
    have hcr : r + d + 1 = c := by omega
    have haSq : a ^ 2 ≤ c ^ 2 := Nat.pow_le_pow_left hac 2
    by_cases hleftDominates : 5 * (2 * q + 3 * r) ≤ 4 * L
    · have hqBound : 7 * q ≤ 6 * b := by omega
      have hcorner := weightedLeftCorner hcEq hcq hqBound
      have hscaled : 9 * (a ^ 2 + b ^ 2) ≤ 2 * L ^ 2 := by
        nlinarith
      have := hscaled.trans hequalEndpoint
      omega
    · have hrightDominates : 4 * L ≤ 5 * (2 * q + 3 * r) := by omega
      have hcoefficient : 8 * c ≤ 4 * b + 5 * r := by omega
      have hcorner := weightedRightCorner hrEq hcr hcoefficient
      have hscaled : 4 * (a ^ 2 + b ^ 2) ≤
          4 * (d + 1) ^ 2 + U ^ 2 := by
        nlinarith
      have := hscaled.trans hrootEndpoint
      omega

/-- The exact arithmetic landing for the weighted pair inequalities. -/
theorem twoCosts_le_rlBudget_of_weightedBounds
    {x y s d p : ℕ}
    (hxy : x ≤ y)
    (hroot : 2 * y ≤ 2 * s + d)
    (hpair : x + 2 * y ≤ 2 * (s + d))
    (hd : 1 ≤ d) (hp : 1 ≤ p) (hratio : 2 * d < s) :
    (x + 1) ^ 2 + (y + 1) ^ 2 ≤
      s * (2 * d + 2 + s) + 2 * s * p := by
  let a := x + 1
  let b := y + 1
  let L := 2 * s + 2 * d + 3
  let U := 2 * s + d + 2
  let R := s ^ 2 + 2 * s * d + 4 * s
  have hab : a ≤ b := by simp only [a, b]; omega
  have habL : a + 2 * b ≤ L := by
    simp only [a, b, L]
    omega
  have hbU : 2 * b ≤ U := by
    simp only [b, U]
    omega
  have hsLower : 2 * d + 1 ≤ s := by omega
  let t := s - (2 * d + 1)
  have hsEq : s = 2 * d + 1 + t := by
    simp only [t]
    omega
  have hequalEndpoint : 2 * L ^ 2 ≤ 9 * R := by
    simp only [L, R]
    rw [hsEq]
    nlinarith [sq_nonneg t]
  have hrootEndpoint : 4 * (d + 1) ^ 2 + U ^ 2 ≤ 4 * R := by
    simp only [U, R]
    rw [hsEq]
    nlinarith [sq_nonneg t]
  have hbase : R ≤ s * (2 * d + 2 + s) + 2 * s * p := by
    have hsp : s ≤ s * p := by
      simpa using Nat.mul_le_mul_left s hp
    simp only [R]
    nlinarith
  have hLU : L = U + d + 1 := by
    simp only [L, U]
    omega
  have habR := weightedConvexInterval hab habL hbU hLU
    hequalEndpoint hrootEndpoint
  simpa [a, b] using habR.trans hbase

/-- The boundary-strength arithmetic landing.  One extra partner unit pays
the closed ratio `2*d = s`; more generally this holds throughout
`2*d <= s` whenever `2 <= p`. -/
theorem twoCosts_le_rlBudget_of_weightedBounds_partner_two
    {x y s d p : ℕ}
    (hxy : x ≤ y)
    (hroot : 2 * y ≤ 2 * s + d)
    (hpair : x + 2 * y ≤ 2 * (s + d))
    (hd : 1 ≤ d) (hp : 2 ≤ p) (hratio : 2 * d ≤ s) :
    (x + 1) ^ 2 + (y + 1) ^ 2 ≤
      s * (2 * d + 2 + s) + 2 * s * p := by
  let a := x + 1
  let b := y + 1
  let L := 2 * s + 2 * d + 3
  let U := 2 * s + d + 2
  let R := s ^ 2 + 2 * s * d + 6 * s
  have hab : a ≤ b := by simp only [a, b]; omega
  have habL : a + 2 * b ≤ L := by
    simp only [a, b, L]
    omega
  have hbU : 2 * b ≤ U := by
    simp only [b, U]
    omega
  let t := s - 2 * d
  have hsEq : s = 2 * d + t := by
    simp only [t]
    omega
  have hequalEndpoint : 2 * L ^ 2 ≤ 9 * R := by
    simp only [L, R]
    rw [hsEq]
    nlinarith [sq_nonneg t]
  have hrootEndpoint : 4 * (d + 1) ^ 2 + U ^ 2 ≤ 4 * R := by
    simp only [U, R]
    rw [hsEq]
    nlinarith [sq_nonneg t]
  have hbase : R ≤ s * (2 * d + 2 + s) + 2 * s * p := by
    have hsp : 2 * s ≤ s * p := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left s hp
    simp only [R]
    nlinarith
  have hLU : L = U + d + 1 := by
    simp only [L, U]
    omega
  have habR := weightedConvexInterval hab habL hbU hLU
    hequalEndpoint hrootEndpoint
  simpa [a, b] using habR.trans hbase

/-- Partner two also pays the first three rows below `s=2d`.  The lower
bound `d>=6` is automatic in the intended strict residual, but is kept
literal at the arithmetic interface. -/
theorem twoCosts_le_rlBudget_of_weightedBounds_partner_two_near
    {x y s d p : ℕ}
    (hxy : x ≤ y)
    (hroot : 2 * y ≤ 2 * s + d)
    (hpair : x + 2 * y ≤ 2 * (s + d))
    (hd : 6 ≤ d) (hp : 2 ≤ p)
    (hbelow : s ≤ 2 * d) (hnear : 2 * d ≤ s + 3) :
    (x + 1) ^ 2 + (y + 1) ^ 2 ≤
      s * (2 * d + 2 + s) + 2 * s * p := by
  let a := x + 1
  let b := y + 1
  let L := 2 * s + 2 * d + 3
  let U := 2 * s + d + 2
  let R := s ^ 2 + 2 * s * d + 6 * s
  have hab : a ≤ b := by simp only [a, b]; omega
  have habL : a + 2 * b ≤ L := by
    simp only [a, b, L]
    omega
  have hbU : 2 * b ≤ U := by
    simp only [b, U]
    omega
  let r := 2 * d - s
  have hsEq : s + r = 2 * d := by
    simp only [r]
    omega
  have hr : r ≤ 3 := by omega
  have hequalEndpoint : 2 * L ^ 2 ≤ 9 * R := by
    simp only [L, R]
    interval_cases r <;> nlinarith
  have hrootEndpoint : 4 * (d + 1) ^ 2 + U ^ 2 ≤ 4 * R := by
    simp only [U, R]
    interval_cases r <;> nlinarith
  have hbase : R ≤ s * (2 * d + 2 + s) + 2 * s * p := by
    have hsp : 2 * s ≤ s * p := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left s hp
    simp only [R]
    nlinarith
  have hLU : L = U + d + 1 := by
    simp only [L, U]
    omega
  have habR := weightedConvexInterval hab habL hbU hLU
    hequalEndpoint hrootEndpoint
  simpa [a, b] using habR.trans hbase

/-- RFC contains the symmetric two-demand cut condition for the two
internal demands themselves. -/
theorem internalTwoDemandCutCondition_of_rootedCutCondition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m₁ m₂ : Fin 2 → V) (w x₀ : V)
    (hRFC : ∀ T : Finset V, w ∉ T →
      (∑ i : Fin 2, separationDemand T (m₁ i) (m₂ i)) +
        (if x₀ ∈ T then 1 else 0) ≤ cutSize G T) :
    TwoDemandCutCondition G (m₁ 0) (m₂ 0) (m₁ 1) (m₂ 1) := by
  classical
  have hsym := symmetricRootedCutCondition_of_rootForm
    G m₁ m₂ w x₀ hRFC
  intro T
  have h := hsym T
  rw [Fin.sum_univ_two] at h
  omega

/-- The internal-pair G-A ledger gives both weighted distance bounds. -/
theorem internalWeightedDistanceBounds_of_rootedCutCondition
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (m₁ m₂ : Fin 2 → V) (w x₀ : V)
    (hconn : G.Connected)
    (hRFC : ∀ T : Finset V, w ∉ T →
      (∑ i : Fin 2, separationDemand T (m₁ i) (m₂ i)) +
        (if x₀ ∈ T then 1 else 0) ≤ cutSize G T) :
    G.dist (m₁ 0) (m₂ 0) + 2 * G.dist (m₁ 1) (m₂ 1) ≤
        2 * (Fintype.card V - 1) ∧
      G.dist (m₁ 1) (m₂ 1) + 2 * G.dist (m₁ 0) (m₂ 0) ≤
        2 * (Fintype.card V - 1) := by
  obtain ⟨Q₀, hQ₀⟩ := hconn.exists_walk_length_eq_dist (m₁ 0) (m₂ 0)
  obtain ⟨Q₁, hQ₁⟩ := hconn.exists_walk_length_eq_dist (m₁ 1) (m₂ 1)
  have hQ₀geo : IsGeodesic Q₀ := hQ₀
  have hQ₁geo : IsGeodesic Q₁ := hQ₁
  have hcut := internalTwoDemandCutCondition_of_rootedCutCondition
    G m₁ m₂ w x₀ hRFC
  have hforward :=
    (gapGA_symmetric_bounds Q₀ Q₁ hQ₀geo hQ₁geo hcut).2
  have hbackward :=
    (gapGA_symmetric_bounds Q₁ Q₀ hQ₁geo hQ₀geo
      (hcut.swapPairs G)).2
  have hcard₀ := hQ₀geo.card_supportFinset
  have hcard₁ := hQ₁geo.card_supportFinset
  have hle₀ : Q₀.length + 1 ≤ Fintype.card V := by
    rw [← hcard₀]
    exact Finset.card_le_univ _
  have hle₁ : Q₁.length + 1 ≤ Fintype.card V := by
    rw [← hcard₁]
    exact Finset.card_le_univ _
  rw [hQ₀, hQ₁] at hforward hbackward
  unfold slack at hforward hbackward
  constructor <;> omega

/-- If a bridge is used by a geodesic for the first demand, the second
demand has both terminals on the same side of that bridge.  This is the
first exact step in the bridge dispatch for strict equal-distance ledgers. -/
theorem TwoDemandCutCondition.not_separates_bridgeSide_second
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b c d u v : V} (hcut : TwoDemandCutCondition G a b c d)
    {P : G.Walk a b} (hP : IsGeodesic P)
    (hbridge : G.IsBridge s(u, v)) (heP : s(u, v) ∈ P.edges) :
    ¬Separates (bridgeSide G u v) c d := by
  intro hsecond
  exact hcut.not_both_separated_by_unit_cut G (bridgeSide G u v)
    (IsBridge.separates_bridgeSide_of_isTrail_mem_edges
      hbridge P hP.isPath.isTrail heP)
    hsecond
    (by rw [IsBridge.cutSize_bridgeSide_eq_one hbridge])

/-- A walk avoiding a bridge cannot change sides of its canonical bridge
cut. -/
theorem IsBridge.mem_bridgeSide_iff_of_walk_edge_not_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {u v a b : V}
    (_hbridge : G.IsBridge s(a, b)) (W : G.Walk u v)
    (havoid : s(a, b) ∉ W.edges) :
    u ∈ bridgeSide G a b ↔ v ∈ bridgeSide G a b := by
  have hWdel : (G.deleteEdges {s(a, b)}).Walk u v :=
    W.toDeleteEdge s(a, b) havoid
  simp only [mem_bridgeSide_iff]
  exact ⟨fun hu => hu.trans hWdel.reachable,
    fun hv => hv.trans hWdel.reverse.reachable⟩

/-- If the initial vertex of a bridge-avoiding walk lies on the canonical
side, then its whole support lies on that side. -/
theorem IsBridge.walk_support_subset_bridgeSide_of_start_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {u v a b : V}
    (hbridge : G.IsBridge s(a, b)) (W : G.Walk u v)
    (hstart : u ∈ bridgeSide G a b)
    (havoid : s(a, b) ∉ W.edges) :
    ∀ x ∈ W.support, x ∈ bridgeSide G a b := by
  intro x hx
  let Wx := W.takeUntil x hx
  have havoidX : s(a, b) ∉ Wx.edges := by
    intro he
    exact havoid (W.edges_takeUntil_subset hx he)
  exact
    (Erdos23GapGBTwoDemandWeighted.IsBridge.mem_bridgeSide_iff_of_walk_edge_not_mem
      hbridge Wx havoidX).1 hstart

/-- Under the two-demand cut condition, a geodesic for the second demand is
entirely contained in one side of every bridge used by the first geodesic. -/
theorem TwoDemandCutCondition.second_geodesic_support_one_bridgeSide
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b c d u v : V} (hcut : TwoDemandCutCondition G a b c d)
    {P : G.Walk a b} {Q : G.Walk c d}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (hbridge : G.IsBridge s(u, v)) (heP : s(u, v) ∈ P.edges) :
    (∀ x ∈ Q.support, x ∈ bridgeSide G u v) ∨
      (∀ x ∈ Q.support, x ∉ bridgeSide G u v) := by
  have hnotsep :=
    Erdos23GapGBTwoDemandWeighted.TwoDemandCutCondition.not_separates_bridgeSide_second
      hcut hP hbridge heP
  have havoid : s(u, v) ∉ Q.edges := by
    intro heQ
    exact hnotsep
      (IsBridge.separates_bridgeSide_of_isTrail_mem_edges
        hbridge Q hQ.isPath.isTrail heQ)
  by_cases hc : c ∈ bridgeSide G u v
  · left
    exact
      Erdos23GapGBTwoDemandWeighted.IsBridge.walk_support_subset_bridgeSide_of_start_mem
        hbridge Q hc havoid
  · right
    intro x hx hxin
    let Qx := Q.takeUntil x hx
    have havoidX : s(u, v) ∉ Qx.edges := by
      intro he
      exact havoid (Q.edges_takeUntil_subset hx he)
    exact hc
      ((Erdos23GapGBTwoDemandWeighted.IsBridge.mem_bridgeSide_iff_of_walk_edge_not_mem
        hbridge Qx havoidX).2 hxin)

/-- The canonical side of a bridge induces a connected graph. -/
theorem IsBridge.connected_induce_bridgeSide
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a b : V} (hbridge : G.IsBridge s(a, b)) :
    (G.induce (bridgeSide G a b : Set V)).Connected := by
  rw [connected_iff_exists_forall_reachable]
  let a' : bridgeSide G a b := ⟨a, by simp⟩
  refine ⟨a', ?_⟩
  rintro ⟨x, hx⟩
  have hr : (G.deleteEdges {s(a, b)}).Reachable a x :=
    (mem_bridgeSide_iff G a b x).1 hx
  obtain ⟨W⟩ := hr
  have hedge : ∀ e, e ∈ W.edges → e ∈ G.edgeSet := by
    intro e he
    exact edgeSet_mono (G.deleteEdges_le {s(a, b)})
      (W.edges_subset_edgeSet he)
  let WG : G.Walk a x := W.transfer G hedge
  have havoid : s(a, b) ∉ WG.edges := by
    intro he
    have heW : s(a, b) ∈ W.edges := by simpa [WG] using he
    have hedel := W.edges_subset_edgeSet heW
    have hab : (G.deleteEdges {s(a, b)}).Adj a b := by simpa using hedel
    simpa using hab
  have hsupport : ∀ z ∈ WG.support, z ∈ bridgeSide G a b :=
    Erdos23GapGBTwoDemandWeighted.IsBridge.walk_support_subset_bridgeSide_of_start_mem
      hbridge WG (by simp) havoid
  exact ⟨WG.induce (bridgeSide G a b : Set V) hsupport⟩

/-- A cut of one induced bridge side which omits the bridge endpoint has the
same capacity in the ambient graph.  There is no ambient crossing edge to
the opposite side because the bridge endpoint itself is not in the cut. -/
theorem IsBridge.cutSize_image_eq_induce_of_endpoint_not_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V} (_hbridge : G.IsBridge s(a, b))
    (T : Finset {x : V // x ∈ (bridgeSide G a b : Set V)})
    (ha : (⟨a, by simp⟩ : {x : V // x ∈ (bridgeSide G a b : Set V)}) ∉ T) :
    cutSize G (T.image Subtype.val) =
      cutSize (G.induce (bridgeSide G a b : Set V)) T := by
  classical
  have hterm : ∀ z ∈ T,
      (G.neighborFinset z.val \ T.image Subtype.val).card =
        ((G.induce (bridgeSide G a b : Set V)).neighborFinset z \ T).card := by
    intro z hz
    have hzne : z.val ≠ a := by
      intro hza
      apply ha
      have hzEq : z =
          (⟨a, by simp⟩ : {x : V // x ∈ (bridgeSide G a b : Set V)}) := by
        apply Subtype.ext
        exact hza
      simpa [hzEq] using hz
    have hneighbors : G.neighborSet z.val ⊆ (bridgeSide G a b : Set V) := by
      intro x hx
      by_contra hxside
      exact hzne
        (eq_endpoints_of_mem_bridgeSide_adj_not_mem z.prop hxside hx).1
    let emb : {x : V // x ∈ (bridgeSide G a b : Set V)} ↪ V := .subtype _
    have hmapNeighbor :
        ((G.induce (bridgeSide G a b : Set V)).neighborFinset z).map emb =
          G.neighborFinset z.val := by
      ext x
      constructor
      · intro hx
        obtain ⟨x', hx', hval⟩ := Finset.mem_map.mp hx
        have hadj : G.Adj z.val x'.val := by simpa using hx'
        have hval' : x'.val = x := by simpa [emb] using hval
        subst x
        simpa using hadj
      · intro hx
        have hadj : G.Adj z.val x := by simpa using hx
        have hxside : x ∈ (bridgeSide G a b : Set V) := hneighbors hadj
        apply Finset.mem_map.mpr
        refine ⟨⟨x, hxside⟩, ?_, ?_⟩
        · simpa using hadj
        · rfl
    have hmapT : T.map emb = T.image Subtype.val := by
      ext x
      simp [emb]
    calc
      (G.neighborFinset z.val \ T.image Subtype.val).card =
          (((G.induce (bridgeSide G a b : Set V)).neighborFinset z).map emb \
            T.map emb).card := by rw [hmapNeighbor, hmapT]
      _ = (((G.induce (bridgeSide G a b : Set V)).neighborFinset z \ T).map emb).card := by
        rw [Finset.map_sdiff]
      _ = ((G.induce (bridgeSide G a b : Set V)).neighborFinset z \ T).card :=
        Finset.card_map _
  unfold cutSize
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro z hz
    exact hterm z hz
  · intro x _ y _ hxy
    exact Subtype.ext hxy

/-- Extend a cut of one bridge side to the ambient graph while keeping the
bridge uncut.  If the bridge endpoint belongs to the cut, include the entire
opposite side; otherwise include no opposite-side vertex. -/
noncomputable def bridgeSideExtension
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (a b : V)
    (T : Finset {x : V // x ∈ (bridgeSide G a b : Set V)}) : Finset V :=
  if (⟨a, by simp⟩ : {x : V // x ∈ (bridgeSide G a b : Set V)}) ∈ T then
    Finset.univ \ ((Finset.univ \ T).image Subtype.val)
  else T.image Subtype.val

@[simp]
theorem mem_bridgeSideExtension_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (a b : V)
    (T : Finset {x : V // x ∈ (bridgeSide G a b : Set V)})
    (x : {x : V // x ∈ (bridgeSide G a b : Set V)}) :
    x.val ∈ bridgeSideExtension G a b T ↔ x ∈ T := by
  classical
  by_cases ha : (⟨a, by simp⟩ :
      {x : V // x ∈ (bridgeSide G a b : Set V)}) ∈ T
  · simp [bridgeSideExtension, ha]
  · simp [bridgeSideExtension, ha]

@[simp]
theorem mem_bridgeSideExtension_iff_endpoint_mem_of_not_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (a b x : V)
    (T : Finset {x : V // x ∈ (bridgeSide G a b : Set V)})
    (hx : x ∉ bridgeSide G a b) :
    x ∈ bridgeSideExtension G a b T ↔
      (⟨a, by simp⟩ : {x : V // x ∈ (bridgeSide G a b : Set V)}) ∈ T := by
  classical
  have houtside : ∀ U : Finset {x : V // x ∈ (bridgeSide G a b : Set V)},
      x ∉ U.image Subtype.val := by
    intro U hxU
    obtain ⟨z, _hz, hzx⟩ := Finset.mem_image.mp hxU
    exact hx (hzx ▸ z.prop)
  by_cases ha : (⟨a, by simp⟩ :
      {x : V // x ∈ (bridgeSide G a b : Set V)}) ∈ T
  · simp [bridgeSideExtension, ha, houtside]
  · simp [bridgeSideExtension, ha, houtside]

/-- The bridge-side extension preserves cut capacity exactly. -/
theorem IsBridge.cutSize_bridgeSideExtension
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V} (hbridge : G.IsBridge s(a, b))
    (T : Finset {x : V // x ∈ (bridgeSide G a b : Set V)}) :
    cutSize G (bridgeSideExtension G a b T) =
      cutSize (G.induce (bridgeSide G a b : Set V)) T := by
  classical
  let a' : {x : V // x ∈ (bridgeSide G a b : Set V)} := ⟨a, by simp⟩
  by_cases ha : a' ∈ T
  · let Tc := Finset.univ \ T
    have haTc : a' ∉ Tc := by simp [Tc, ha]
    have hcap :=
      Erdos23GapGBTwoDemandWeighted.IsBridge.cutSize_image_eq_induce_of_endpoint_not_mem
        hbridge Tc haTc
    have hamb := cutSize_univ_sdiff G (Tc.image Subtype.val)
    have hind := cutSize_univ_sdiff
      (G.induce (bridgeSide G a b : Set V)) Tc
    have hTcComp : Finset.univ \ Tc = T := by
      ext z
      simp [Tc]
    rw [hTcComp] at hind
    rw [show bridgeSideExtension G a b T =
        Finset.univ \ Tc.image Subtype.val by simp [bridgeSideExtension, a', ha, Tc]]
    rw [hamb, hcap]
    exact hind.symm
  · simpa [bridgeSideExtension, a', ha] using
      Erdos23GapGBTwoDemandWeighted.IsBridge.cutSize_image_eq_induce_of_endpoint_not_mem
        hbridge T ha

/-- Restrict a two-demand cut condition to one bridge side.  The first
ambient demand is truncated at the bridge endpoint; the second demand is
retained when both of its terminals lie on this side. -/
theorem TwoDemandCutCondition.induce_bridgeSide
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x c d a b : V} (hcut : TwoDemandCutCondition G w x c d)
    (hbridge : G.IsBridge s(a, b))
    (hw : w ∈ bridgeSide G a b) (hx : x ∉ bridgeSide G a b)
    (hc : c ∈ bridgeSide G a b) (hd : d ∈ bridgeSide G a b) :
    TwoDemandCutCondition (G.induce (bridgeSide G a b : Set V))
      ⟨w, hw⟩ ⟨a, by simp⟩ ⟨c, hc⟩ ⟨d, hd⟩ := by
  classical
  intro T
  let S := bridgeSideExtension G a b T
  let w' : {z : V // z ∈ (bridgeSide G a b : Set V)} := ⟨w, hw⟩
  let a' : {z : V // z ∈ (bridgeSide G a b : Set V)} := ⟨a, by simp⟩
  let c' : {z : V // z ∈ (bridgeSide G a b : Set V)} := ⟨c, hc⟩
  let d' : {z : V // z ∈ (bridgeSide G a b : Set V)} := ⟨d, hd⟩
  have hwS : w ∈ S ↔ w' ∈ T := by
    simpa [S, w'] using mem_bridgeSideExtension_iff G a b T w'
  have hxS : x ∈ S ↔ a' ∈ T := by
    simpa [S, a'] using
      mem_bridgeSideExtension_iff_endpoint_mem_of_not_mem G a b x T hx
  have hcS : c ∈ S ↔ c' ∈ T := by
    simpa [S, c'] using mem_bridgeSideExtension_iff G a b T c'
  have hdS : d ∈ S ↔ d' ∈ T := by
    simpa [S, d'] using mem_bridgeSideExtension_iff G a b T d'
  have hfirst : separationDemand S w x = separationDemand T w' a' := by
    by_cases hW : w' ∈ T <;> by_cases hA : a' ∈ T <;>
      simp [separationDemand, hwS, hxS, hW, hA]
  have hsecond : separationDemand S c d = separationDemand T c' d' := by
    by_cases hC : c' ∈ T <;> by_cases hD : d' ∈ T <;>
      simp [separationDemand, hcS, hdS, hC, hD]
  have hcap : cutSize G S =
      cutSize (G.induce (bridgeSide G a b : Set V)) T := by
    simpa [S] using
      Erdos23GapGBTwoDemandWeighted.IsBridge.cutSize_bridgeSideExtension
        hbridge T
  have hglobal := hcut S
  change separationDemand T w' a' + separationDemand T c' d' ≤
    cutSize (G.induce (bridgeSide G a b : Set V)) T
  rw [← hfirst, ← hsecond, ← hcap]
  exact hglobal

/-- Inducing a walk on a set containing its support preserves its length. -/
theorem Walk.length_induce_of_support_subset
    {V : Type*} {G : SimpleGraph V} {u v : V} (P : G.Walk u v)
    (S : Set V) (hS : ∀ x ∈ P.support, x ∈ S) :
    (P.induce S hS).length = P.length := by
  let P' := P.induce S hS
  have hlen := P'.length_map (Embedding.induce S).toHom
  have hmap : P'.map (Embedding.induce S).toHom = P := by
    simpa [P'] using Walk.map_induce P hS
  rw [hmap] at hlen
  exact hlen.symm

/-- A geodesic wholly contained in a vertex set remains geodesic in the
induced graph. -/
theorem IsGeodesic.induce_of_support_subset
    {V : Type*} {G : SimpleGraph V} {u v : V} {P : G.Walk u v}
    (hP : IsGeodesic P) (S : Set V) (hS : ∀ x ∈ P.support, x ∈ S) :
    IsGeodesic (P.induce S hS) := by
  let P' := P.induce S hS
  have hupper : (G.induce S).dist
      ⟨u, hS u P.start_mem_support⟩ ⟨v, hS v P.end_mem_support⟩ ≤ P'.length :=
    dist_le P'
  obtain ⟨R, hR⟩ := P'.reachable.exists_walk_length_eq_dist
  let Rmap : G.Walk u v := R.map (Embedding.induce S).toHom
  have hlower : G.dist u v ≤ Rmap.length := dist_le Rmap
  have hPlength : P'.length = P.length :=
    Erdos23GapGBTwoDemandWeighted.Walk.length_induce_of_support_subset P S hS
  have hRlength : Rmap.length = R.length := by
    exact R.length_map (Embedding.induce S).toHom
  unfold IsGeodesic at hP ⊢
  change P'.length =
    (G.induce S).dist
      ⟨u, hS u P.start_mem_support⟩ ⟨v, hS v P.end_mem_support⟩
  rw [hPlength]
  rw [hP]
  rw [hRlength] at hlower
  rw [hR] at hlower
  omega

/-- Exact arithmetic contradiction behind the bridge dispatch.  `sideOrder`
is the order of the induced side containing a prefix of length `i`; the
opposite suffix contributes `D-i` vertices outside that side. -/
theorem no_bridge_of_equalLedger_sideSE2
    {n D i sideOrder : ℕ}
    (hequality : 3 * D = 2 * (n - 1)) (hi : i < D)
    (hsideCard : sideOrder + (D - i) ≤ n)
    (hsideSE2 : 2 * D ≤ 2 * (sideOrder - 1 - i) + i) : False := by
  omega

/-! ## Strictness on the equal-distance, double-slack face

The ordinary G-A ledger allows equality `D = 2 * slack P`.  In the
all-nonbridge equality geometry, however, the even-tile decomposition makes
the two ends of `P` the unique pair at distance `P.length`.  The following
small position record packages the two anchors needed for that assertion.
-/

/-- Position of a vertex in the chain of even tiles on the double-slack
all-nonbridge face.  A vertex is within one edge of its left even anchor; if
it is not that anchor, it is within one edge of the next even anchor too. -/
structure DoubleSlackPosition
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ : V} (P : G.Walk w x₀) (x : V) where
  block : ℕ
  block_le : block ≤ slack P
  left_anchor_dist : G.dist x (P.getVert (2 * block)) ≤ 1
  next_anchor : block < slack P →
    x = P.getVert (2 * block) ∨
      G.dist x (P.getVert (2 * (block + 1))) ≤ 1
  terminal_eq : block = slack P → x = P.getVert (2 * slack P)

/-- Every vertex has the two-sided position record supplied by the rigid
chain of even two-edge tiles. -/
theorem IsGeodesic.exists_doubleSlackPosition
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ x : V} {P : G.Walk w x₀}
    (hP : IsGeodesic P) (hdouble : P.length = 2 * slack P)
    (hnonbridge : ∀ i < P.length,
      ¬G.IsBridge s(P.getVert i, P.getVert (i + 1))) :
    Nonempty (DoubleSlackPosition P x) := by
  classical
  by_cases hx : x ∈ P.support
  · let j := P.support.idxOf x
    let k := j / 2
    have hjle : j ≤ P.length := support_idxOf_le_length P hx
    have hget : P.getVert j = x := P.getVert_support_idxOf hx
    have hmod := Nat.mod_add_div j 2
    have hmodlt : j % 2 < 2 := Nat.mod_lt _ (by omega)
    have hk : k ≤ slack P := by
      simp only [k]
      rw [hdouble] at hjle
      omega
    have hleftIndex : 2 * k ≤ j := by
      simp only [k]
      omega
    have hleftDist : G.dist x (P.getVert (2 * k)) ≤ 1 := by
      have hd := hP.dist_getVert_eq_sub hleftIndex hjle
      rw [hget] at hd
      rw [dist_comm, hd]
      simp only [k]
      omega
    refine ⟨{
      block := k
      block_le := hk
      left_anchor_dist := hleftDist
      next_anchor := ?_
      terminal_eq := ?_ }⟩
    · intro hks
      by_cases heven : j % 2 = 0
      · left
        calc
          x = P.getVert j := hget.symm
          _ = P.getVert (2 * k) := by congr 1; simp only [k]; omega
      · right
        have hodd : j % 2 = 1 := by omega
        have hjnext : j ≤ 2 * (k + 1) := by
          simp only [k]
          omega
        have hnextLe : 2 * (k + 1) ≤ P.length := by
          rw [hdouble]
          omega
        have hd := hP.dist_getVert_eq_sub hjnext hnextLe
        rw [hget] at hd
        rw [hd]
        simp only [k]
        omega
    · intro hterminal
      have hj : j = 2 * slack P := by
        simp only [k] at hterminal
        rw [hdouble] at hjle
        omega
      calc
        x = P.getVert j := hget.symm
        _ = P.getVert (2 * slack P) := by rw [hj]
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
    obtain ⟨hleft, hright, _hbounds⟩ :=
      attachment_extrema_of_interval_eq_two P C (2 * k) (by
        simpa [Nat.add_assoc] using htile)
    obtain ⟨_hlenL, cL, hcL, hAdjL⟩ :=
      (mem_offCorridorAttachmentIndices P C (2 * k)).1 hleft
    obtain ⟨_hlenR, cR, hcR, hAdjR⟩ :=
      (mem_offCorridorAttachmentIndices P C (2 * k + 2)).1 hright
    have hcLx : cL = x := by simpa [hcset] using hcL
    have hcRx : cR = x := by simpa [hcset] using hcR
    subst cL
    subst cR
    refine ⟨{
      block := k
      block_le := hk.le
      left_anchor_dist := by rw [dist_eq_one_iff_adj.mpr hAdjL]
      next_anchor := ?_
      terminal_eq := by intro; omega }⟩
    intro _
    right
    have hindex : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [hindex, dist_eq_one_iff_adj.mpr hAdjR]

/-- On the rigid double-slack all-nonbridge face, the corridor terminals are
the unique unordered pair at the corridor diameter. -/
theorem IsGeodesic.eq_corridorEndpoints_of_dist_eq_length_doubleSlack
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {w x₀ x y : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P)
    (hdouble : P.length = 2 * slack P) (hs : 2 ≤ slack P)
    (hnonbridge : ∀ i < P.length,
      ¬G.IsBridge s(P.getVert i, P.getVert (i + 1)))
    (hxy : G.dist x y = P.length) :
    (x = P.getVert 0 ∧ y = P.getVert (2 * slack P)) ∨
      (y = P.getVert 0 ∧ x = P.getVert (2 * slack P)) := by
  let px := Classical.choice
    (Erdos23GapGBTwoDemandWeighted.IsGeodesic.exists_doubleSlackPosition
      hP hdouble hnonbridge (x := x))
  let py := Classical.choice
    (Erdos23GapGBTwoDemandWeighted.IsGeodesic.exists_doubleSlackPosition
      hP hdouble hnonbridge (x := y))
  have hlen : G.dist x y = 2 * slack P := by omega
  have hanchors {i j : ℕ} (hij : i ≤ j)
      (hj : j ≤ slack P) :
      G.dist (P.getVert (2 * i)) (P.getVert (2 * j)) = 2 * (j - i) := by
    have hd := hP.dist_getVert_eq_sub (i := 2 * i) (j := 2 * j)
      (by omega) (by rw [hdouble]; omega)
    rw [hd]
    omega
  have ordered {u v : V} (pu : DoubleSlackPosition P u)
      (pv : DoubleSlackPosition P v)
      (huv : G.dist u v = 2 * slack P)
      (hab : pu.block ≤ pv.block) :
      u = P.getVert 0 ∧ v = P.getVert (2 * slack P) := by
    let a := pu.block
    let b := pv.block
    have ha : a ≤ slack P := pu.block_le
    have hb : b ≤ slack P := pv.block_le
    have hab' : a ≤ b := hab
    have hleftU : G.dist u (P.getVert (2 * a)) ≤ 1 := by
      simpa [a] using pu.left_anchor_dist
    have hleftV : G.dist v (P.getVert (2 * b)) ≤ 1 := by
      simpa [b] using pv.left_anchor_dist
    have hrightV : G.dist (P.getVert (2 * b)) v ≤ 1 := by
      simpa [SimpleGraph.dist_comm] using hleftV
    have ha0 : a = 0 := by
      by_contra hane
      have ha1 : 1 ≤ a := by omega
      by_cases hbs : b = slack P
      · have hv : v = P.getVert (2 * slack P) := pv.terminal_eq hbs
        have htri : G.dist u v ≤
            G.dist u (P.getVert (2 * a)) +
              G.dist (P.getVert (2 * a)) v := hconn.dist_triangle
        have hanchor := hanchors (i := a) (j := slack P) (by omega) (by omega)
        rw [huv, hv, hanchor] at htri
        omega
      · have hblt : b < slack P := by omega
        have htri₁ : G.dist u v ≤
            G.dist u (P.getVert (2 * a)) +
              G.dist (P.getVert (2 * a)) v := hconn.dist_triangle
        have htri₂ : G.dist (P.getVert (2 * a)) v ≤
            G.dist (P.getVert (2 * a)) (P.getVert (2 * b)) +
              G.dist (P.getVert (2 * b)) v := hconn.dist_triangle
        have hanchor := hanchors hab' hb
        rw [huv] at htri₁
        rw [hanchor] at htri₂
        omega
    have hbs : b = slack P := by
      by_contra hbne
      have hblt : b < slack P := by omega
      have halt : pu.block < slack P := by
        simpa [a] using (show a < slack P by omega)
      rcases pu.next_anchor halt with hu0 | hunext
      · have hu0' : u = P.getVert (2 * a) := by simpa [a] using hu0
        have htri : G.dist u v ≤
            G.dist u (P.getVert (2 * b)) +
              G.dist (P.getVert (2 * b)) v := hconn.dist_triangle
        have hanchor := hanchors (i := 0) (j := b) (by omega) hb
        rw [huv, hu0', ha0, hanchor] at htri
        omega
      · by_cases hb0 : b = 0
        · have htri : G.dist u v ≤
              G.dist u (P.getVert 0) + G.dist (P.getVert 0) v :=
            hconn.dist_triangle
          have hleftU0 : G.dist u (P.getVert 0) ≤ 1 := by
            simpa [ha0] using hleftU
          have hleftV0 : G.dist (P.getVert 0) v ≤ 1 := by
            have hleftV' := hleftV
            rw [hb0] at hleftV'
            simpa [SimpleGraph.dist_comm] using hleftV'
          rw [huv] at htri
          omega
        · have hb1 : 1 ≤ b := by omega
          have htri₁ : G.dist u v ≤
              G.dist u (P.getVert 2) + G.dist (P.getVert 2) v :=
            hconn.dist_triangle
          have htri₂ : G.dist (P.getVert 2) v ≤
              G.dist (P.getVert 2) (P.getVert (2 * b)) +
                G.dist (P.getVert (2 * b)) v := hconn.dist_triangle
          have hanchor := hanchors (i := 1) (j := b) hb1 hb
          rw [huv] at htri₁
          rw [hanchor] at htri₂
          have hunext' : G.dist u (P.getVert 2) ≤ 1 := by
            simpa [a, ha0] using hunext
          omega
    have hvEnd : v = P.getVert (2 * slack P) := pv.terminal_eq hbs
    have huStart : u = P.getVert 0 := by
      have halt : pu.block < slack P := by
        simpa [a] using (show a < slack P by omega)
      rcases pu.next_anchor halt with hu0 | hunext
      · simpa [a, ha0] using hu0
      · have htri : G.dist u v ≤
            G.dist u (P.getVert 2) + G.dist (P.getVert 2) v :=
          hconn.dist_triangle
        have hanchor := hanchors (i := 1) (j := slack P) (by omega) (by omega)
        rw [huv, hvEnd, hanchor] at htri
        have hunext' : G.dist u (P.getVert 2) ≤ 1 := by
          simpa [a, ha0] using hunext
        omega
    exact ⟨huStart, hvEnd⟩
  rcases le_total px.block py.block with hab | hba
  · exact Or.inl (ordered px py hlen hab)
  · have hyx : G.dist y x = 2 * slack P := by
      rw [SimpleGraph.dist_comm]
      exact hlen
    exact Or.inr (ordered py px hyx hba)

/-- Distinct equal even demands cannot attain equality in the G-A weighted
order bound when the first geodesic is all-nonbridge.  This is the strict
`3D ≤ 2(n-2)` inequality needed at the sole odd boundary corner. -/
theorem three_mul_equalLength_le_card_sub_two_of_allNonbridge
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b c d : V} {P : G.Walk a b} {Q : G.Walk c d}
    (hconn : G.Connected) (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (hcut : TwoDemandCutCondition G a b c d)
    (heven : Even P.length) (hlegal : 4 ≤ P.length)
    (heq : Q.length = P.length) (hdistinct : s(a, b) ≠ s(c, d))
    (hnonbridge : ∀ i < P.length,
      ¬G.IsBridge s(P.getVert i, P.getVert (i + 1))) :
    3 * P.length ≤ 2 * (Fintype.card V - 2) := by
  have hbounds := gapGA_symmetric_bounds P Q hP hQ hcut
  have hcard := hP.length_lt_card
  by_contra hstrict
  have hequality : 3 * P.length = 2 * (Fintype.card V - 1) := by
    rcases heven with ⟨k, hk⟩
    rw [heq] at hbounds
    unfold slack at hbounds
    omega
  have hdouble : P.length = 2 * slack P := by
    unfold slack
    omega
  have hs : 2 ≤ slack P := by omega
  have hdiam : G.dist c d = P.length := by rw [← hQ, heq]
  have hendpoints :=
    Erdos23GapGBTwoDemandWeighted.IsGeodesic.eq_corridorEndpoints_of_dist_eq_length_doubleSlack
      hconn hP hdouble hs hnonbridge hdiam
  have hstart : P.getVert 0 = a := by simp
  have hend : P.getVert (2 * slack P) = b := by
    rw [← hdouble]
    simp
  rcases hendpoints with hforward | hbackward
  · apply hdistinct
    apply Sym2.eq_iff.mpr
    left
    exact ⟨by simpa [hstart] using hforward.1.symm,
      by simpa [hend] using hforward.2.symm⟩
  · apply hdistinct
    apply Sym2.eq_iff.mpr
    right
    exact ⟨by simpa [hstart] using hbackward.1.symm,
      by simpa [hend] using hbackward.2.symm⟩

/-- Complete graph-level two-demand closure in the long-slack ratio
`2*d < s`.  No joint distance-sum estimate is assumed. -/
theorem totalCost_le_rlBudget_of_twoDemands_twoLength_lt_slack
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    (m₁ m₂ : Fin 2 → V)
    (hconn : G.Connected) (hP : IsGeodesic P)
    (hRFC : ∀ T : Finset V, w ∉ T →
      (∑ i : Fin 2, separationDemand T (m₁ i) (m₂ i)) +
        (if x₀ ∈ T then 1 else 0) ≤ cutSize G T)
    (hd : 1 ≤ P.length) (hratio : 2 * P.length < slack P) :
    (∑ i : Fin 2, (G.dist (m₁ i) (m₂ i) + 1) ^ 2) ≤
      rlBudget (slack P) P.length := by
  let D₀ := G.dist (m₁ 0) (m₂ 0)
  let D₁ := G.dist (m₁ 1) (m₂ 1)
  have hweighted := internalWeightedDistanceBounds_of_rootedCutCondition
    m₁ m₂ w x₀ hconn hRFC
  have hcardP := hP.card_supportFinset
  have hlength : P.length + 1 ≤ Fintype.card V := by
    rw [← hcardP]
    exact Finset.card_le_univ _
  have hsize : Fintype.card V - 1 = slack P + P.length := by
    unfold slack
    omega
  rw [hsize] at hweighted
  have hSE2₀ :=
    two_mul_dist_le_twice_slack_add_length_of_rootedCutCondition
      m₁ m₂ hconn hP hRFC (0 : Fin 2)
  have hSE2₁ :=
    two_mul_dist_le_twice_slack_add_length_of_rootedCutCondition
      m₁ m₂ hconn hP hRFC (1 : Fin 2)
  have hp := partnerDistance_pos P.length
  rcases le_total D₀ D₁ with horder | horder
  · have harith := twoCosts_le_rlBudget_of_weightedBounds
      horder hSE2₁ hweighted.1 hd hp hratio
    simpa [D₀, D₁, Fin.sum_univ_two, rlBudget, add_comm,
      add_left_comm, add_assoc] using harith
  · have harith := twoCosts_le_rlBudget_of_weightedBounds
      horder hSE2₀ hweighted.2 hd hp hratio
    simpa [D₀, D₁, Fin.sum_univ_two, rlBudget, add_comm,
      add_left_comm, add_assoc] using harith

/-- The same graph closure on the closed ratio `2*d <= s` when the root
distance is even.  Positive even root distance has partner distance two,
which supplies the exact endpoint correction. -/
theorem totalCost_le_rlBudget_of_twoDemands_twoLength_le_slack_of_even
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    (m₁ m₂ : Fin 2 → V)
    (hconn : G.Connected) (hP : IsGeodesic P)
    (hRFC : ∀ T : Finset V, w ∉ T →
      (∑ i : Fin 2, separationDemand T (m₁ i) (m₂ i)) +
        (if x₀ ∈ T then 1 else 0) ≤ cutSize G T)
    (hd : 1 ≤ P.length) (heven : Even P.length)
    (hratio : 2 * P.length ≤ slack P) :
    (∑ i : Fin 2, (G.dist (m₁ i) (m₂ i) + 1) ^ 2) ≤
      rlBudget (slack P) P.length := by
  let D₀ := G.dist (m₁ 0) (m₂ 0)
  let D₁ := G.dist (m₁ 1) (m₂ 1)
  have hweighted := internalWeightedDistanceBounds_of_rootedCutCondition
    m₁ m₂ w x₀ hconn hRFC
  have hcardP := hP.card_supportFinset
  have hlength : P.length + 1 ≤ Fintype.card V := by
    rw [← hcardP]
    exact Finset.card_le_univ _
  have hsize : Fintype.card V - 1 = slack P + P.length := by
    unfold slack
    omega
  rw [hsize] at hweighted
  have hSE2₀ :=
    two_mul_dist_le_twice_slack_add_length_of_rootedCutCondition
      m₁ m₂ hconn hP hRFC (0 : Fin 2)
  have hSE2₁ :=
    two_mul_dist_le_twice_slack_add_length_of_rootedCutCondition
      m₁ m₂ hconn hP hRFC (1 : Fin 2)
  obtain ⟨k, hk⟩ := heven
  have hdne : P.length ≠ 1 := by omega
  have hmod : P.length % 2 = 0 := by
    rw [hk]
    omega
  have hpEq : partnerDistance P.length = 2 := by
    simp [partnerDistance, hdne, hmod]
  have hp : 2 ≤ partnerDistance P.length := by rw [hpEq]
  rcases le_total D₀ D₁ with horder | horder
  · have harith := twoCosts_le_rlBudget_of_weightedBounds_partner_two
      horder hSE2₁ hweighted.1 hd hp hratio
    simpa [D₀, D₁, Fin.sum_univ_two, rlBudget, add_comm,
      add_left_comm, add_assoc] using harith
  · have harith := twoCosts_le_rlBudget_of_weightedBounds_partner_two
      horder hSE2₀ hweighted.2 hd hp hratio
    simpa [D₀, D₁, Fin.sum_univ_two, rlBudget, add_comm,
      add_left_comm, add_assoc] using harith

/-- Graph-level partner-two closure for the first three rows below
`s=2d`. -/
theorem totalCost_le_rlBudget_of_twoDemands_even_near_twiceLength
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    (m₁ m₂ : Fin 2 → V)
    (hconn : G.Connected) (hP : IsGeodesic P)
    (hRFC : ∀ T : Finset V, w ∉ T →
      (∑ i : Fin 2, separationDemand T (m₁ i) (m₂ i)) +
        (if x₀ ∈ T then 1 else 0) ≤ cutSize G T)
    (hd : 6 ≤ P.length) (heven : Even P.length)
    (hbelow : slack P ≤ 2 * P.length)
    (hnear : 2 * P.length ≤ slack P + 3) :
    (∑ i : Fin 2, (G.dist (m₁ i) (m₂ i) + 1) ^ 2) ≤
      rlBudget (slack P) P.length := by
  let D₀ := G.dist (m₁ 0) (m₂ 0)
  let D₁ := G.dist (m₁ 1) (m₂ 1)
  have hweighted := internalWeightedDistanceBounds_of_rootedCutCondition
    m₁ m₂ w x₀ hconn hRFC
  have hcardP := hP.card_supportFinset
  have hlength : P.length + 1 ≤ Fintype.card V := by
    rw [← hcardP]
    exact Finset.card_le_univ _
  have hsize : Fintype.card V - 1 = slack P + P.length := by
    unfold slack
    omega
  rw [hsize] at hweighted
  have hSE2₀ :=
    two_mul_dist_le_twice_slack_add_length_of_rootedCutCondition
      m₁ m₂ hconn hP hRFC (0 : Fin 2)
  have hSE2₁ :=
    two_mul_dist_le_twice_slack_add_length_of_rootedCutCondition
      m₁ m₂ hconn hP hRFC (1 : Fin 2)
  obtain ⟨k, hk⟩ := heven
  have hdne : P.length ≠ 1 := by omega
  have hmod : P.length % 2 = 0 := by rw [hk]; omega
  have hpEq : partnerDistance P.length = 2 := by
    simp [partnerDistance, hdne, hmod]
  have hp : 2 ≤ partnerDistance P.length := by rw [hpEq]
  rcases le_total D₀ D₁ with horder | horder
  · have harith := twoCosts_le_rlBudget_of_weightedBounds_partner_two_near
      horder hSE2₁ hweighted.1 hd hp hbelow hnear
    simpa [D₀, D₁, Fin.sum_univ_two, rlBudget, add_comm,
      add_left_comm, add_assoc] using harith
  · have harith := twoCosts_le_rlBudget_of_weightedBounds_partner_two_near
      horder hSE2₀ hweighted.2 hd hp hbelow hnear
    simpa [D₀, D₁, Fin.sum_univ_two, rlBudget, add_comm,
      add_left_comm, add_assoc] using harith

#print axioms twoCosts_le_rlBudget_of_weightedBounds
#print axioms twoCosts_le_rlBudget_of_weightedBounds_partner_two
#print axioms twoCosts_le_rlBudget_of_weightedBounds_partner_two_near
#print axioms internalTwoDemandCutCondition_of_rootedCutCondition
#print axioms internalWeightedDistanceBounds_of_rootedCutCondition
#print axioms TwoDemandCutCondition.not_separates_bridgeSide_second
#print axioms IsBridge.mem_bridgeSide_iff_of_walk_edge_not_mem
#print axioms IsBridge.walk_support_subset_bridgeSide_of_start_mem
#print axioms TwoDemandCutCondition.second_geodesic_support_one_bridgeSide
#print axioms IsBridge.connected_induce_bridgeSide
#print axioms IsBridge.cutSize_image_eq_induce_of_endpoint_not_mem
#print axioms mem_bridgeSideExtension_iff
#print axioms mem_bridgeSideExtension_iff_endpoint_mem_of_not_mem
#print axioms IsBridge.cutSize_bridgeSideExtension
#print axioms TwoDemandCutCondition.induce_bridgeSide
#print axioms IsGeodesic.induce_of_support_subset
#print axioms IsGeodesic.exists_doubleSlackPosition
#print axioms IsGeodesic.eq_corridorEndpoints_of_dist_eq_length_doubleSlack
#print axioms three_mul_equalLength_le_card_sub_two_of_allNonbridge
#print axioms totalCost_le_rlBudget_of_twoDemands_twoLength_lt_slack
#print axioms totalCost_le_rlBudget_of_twoDemands_twoLength_le_slack_of_even
#print axioms totalCost_le_rlBudget_of_twoDemands_even_near_twiceLength

end Erdos23GapGBTwoDemandWeighted
