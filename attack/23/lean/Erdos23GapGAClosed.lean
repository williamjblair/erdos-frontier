/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair, OpenAI Codex
-/
import ErdosProblems.Erdos23GapGACanonical

/-!
# Erdős 23 gap G-A: unconditional closure

The canonical ride/excursion construction is now available for every pair of
finite geodesics.  This file composes it with the already-verified component
ledger interface and records the two exact single-edge laws `SE1` and `SE2`
under the symmetric two-demand cut condition.
-/

namespace Erdos23GapGA

open SimpleGraph

variable {V : Type*}

/-- Unconditional metric consequence of the canonical construction. -/
theorem canonical_length_le_twice_slack
    [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {w x₀ y z : V} {P : G.Walk w x₀} {Q : G.Walk y z}
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (hnonbridge : ∀ {a b : V}, s(a, b) ∈ P.edges →
      s(a, b) ∈ Q.edges → ¬G.IsBridge s(a, b)) :
    Q.length ≤ 2 * slack P :=
  length_le_twice_slack_of_canonicalChargeTheorem
    (canonicalChargeTheorem G) hP hQ hnonbridge

/-- The original cut-condition ledger theorem is now unconditional. -/
theorem canonical_ledgerTheorem
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (w x₀ y z : V) : LedgerTheorem G w x₀ y z :=
  ledgerTheorem_of_canonicalChargeTheorem G (canonicalChargeTheorem G)
    w x₀ y z

/-- **Gap G-A, SE1 and SE2.**  For two geodesics satisfying the symmetric
two-demand cut condition, the second length `D` obeys both

`D ≤ 2s` and `2D ≤ 2s+d`,

where `s=slack P` and `d=P.length`. -/
theorem gapGA_symmetric_bounds
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ y z : V} (P : G.Walk w x₀) (Q : G.Walk y z)
    (hP : IsGeodesic P) (hQ : IsGeodesic Q)
    (hcut : TwoDemandCutCondition G w x₀ y z) :
    Q.length ≤ 2 * slack P ∧
      2 * Q.length ≤ 2 * slack P + P.length := by
  obtain ⟨L⟩ := canonical_ledgerTheorem G w x₀ y z P Q hP hQ hcut
  obtain ⟨Lswap⟩ := canonical_ledgerTheorem G y z w x₀ Q P hQ hP
    (hcut.swapPairs G)
  exact L.symmetric_bounds Lswap

end Erdos23GapGA
