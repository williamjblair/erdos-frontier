import ErdosProblems.Erdos23GapGBJoint

/-!
# A strict BF-RL subregime: one internal demand per off-corridor component

This file contains only the arithmetic landing theorem.  In the graph
application, `resource i` is the order of the off-corridor component
containing demand `i`.  Connectedness gives `D i + 1 <= resource i`; if no
component owns two demands, the exact component partition gives
`sum resource <= s`.  The theorem pays their entire quadratic cost from the
`s^2` term of the RL budget.
-/

open scoped BigOperators

namespace Erdos23QuotientAggregation

open Erdos23GapGBJoint
open Erdos23GapGBSeries

/-- If every demand is housed in a disjoint vertex resource of order at
least its geodesic order, the `s^2` part of the RL budget pays all demands.
This is the arithmetic closure for the graph subregime in which every
M-edge is internal to an off-corridor component and no component contains
two M-edges. -/
theorem totalCost_le_rlBudget_of_disjoint_componentResources
    {I : Type*} [Fintype I] (D resource : I → ℕ) (s d : ℕ)
    (hpack : (∑ i : I, resource i) ≤ s)
    (hdistance : ∀ i, D i + 1 ≤ resource i) :
    (∑ i : I, (D i + 1) ^ 2) ≤ rlBudget s d := by
  let R := ∑ i : I, resource i
  have hterm : ∀ i, (D i + 1) ^ 2 ≤ resource i ^ 2 := by
    intro i
    exact Nat.pow_le_pow_left (hdistance i) 2
  have hsumTerm : (∑ i : I, (D i + 1) ^ 2) ≤
      ∑ i : I, resource i ^ 2 := by
    exact Finset.sum_le_sum fun i _ => hterm i
  have hsquares : (∑ i : I, resource i ^ 2) ≤ R ^ 2 := by
    simpa [R] using
      (Finset.sum_sq_le_sq_sum_of_nonneg
        (s := (Finset.univ : Finset I)) (f := resource)
        (fun _ _ => Nat.zero_le _))
  have hRsq : R ^ 2 ≤ s ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hpack hpack
  have hsBudget : s ^ 2 ≤ rlBudget s d := by
    unfold rlBudget
    nlinarith [partnerDistance_pos d]
  exact hsumTerm.trans (hsquares.trans (hRsq.trans hsBudget))

/-- Exact order of the private-path completion.  It retains every distinct
M-endpoint and inserts `D_i-1` private internal vertices on the B-path
assigned to demand `i`. -/
def privatePathOrder {I : Type*} [Fintype I]
    (endpointCount : ℕ) (D : I → ℕ) : ℕ :=
  endpointCount + ∑ i : I, (D i - 1)

/-- In excess coordinates `D_i=x_i+4`, the private completion order is the
joint cross-term `endpointCount + sum x_i + 3|M|`. -/
theorem privatePathOrder_eq_excess_crossTerm
    {I : Type*} [Fintype I]
    (endpointCount : ℕ) (D excess : I → ℕ)
    (hD : ∀ i, D i = excess i + 4) :
    privatePathOrder endpointCount D =
      endpointCount + (∑ i : I, excess i) + 3 * Fintype.card I := by
  have hterm : ∀ i, D i - 1 = excess i + 3 := by
    intro i
    rw [hD i]
    omega
  unfold privatePathOrder
  calc
    endpointCount + ∑ i : I, (D i - 1) =
        endpointCount + ∑ i : I, (excess i + 3) := by
          apply congrArg (endpointCount + ·)
          apply Finset.sum_congr rfl
          intro i _
          exact hterm i
    _ = endpointCount + (∑ i : I, excess i) +
        3 * Fintype.card I := by
          simp [Finset.sum_add_distrib]
          omega

/-- The abstract cut-count landing used by the private-path construction:
one edge-disjoint B-path pays each crossing M-edge. -/
theorem cutCondition_of_privatePathPayments
    {I : Type*} [Fintype I]
    (mCross pathCross : I → ℕ) (extraSupply : ℕ)
    (hpay : ∀ i, mCross i ≤ pathCross i) :
    (∑ i : I, mCross i) ≤
      (∑ i : I, pathCross i) + extraSupply := by
  calc
    (∑ i : I, mCross i) ≤ ∑ i : I, pathCross i := by
      exact Finset.sum_le_sum fun i _ => hpay i
    _ ≤ (∑ i : I, pathCross i) + extraSupply := Nat.le_add_right _ _

/-- In the strict RL residual, a private completion whose square fits the
RL budget is automatically a strict subinstance.  This is the exact
induction-size gate; no same-order Gamma invocation is possible. -/
theorem privatePathOrder_lt_ambient_of_sq_le_rlBudget
    {n s d completionOrder : ℕ}
    (hsize : n = d + 1 + s)
    (hresidual : 2 * s * partnerDistance d < (d + 1) ^ 2)
    (hfit : completionOrder ^ 2 ≤ rlBudget s d) :
    completionOrder < n := by
  have hbudget : rlBudget s d < n ^ 2 := by
    unfold rlBudget
    rw [hsize]
    nlinarith
  have hsquare : completionOrder ^ 2 < n ^ 2 := hfit.trans_lt hbudget
  nlinarith

/-- Once strict Gamma induction supplies the Gamma bound on the explicit
private-path completion, its square-fit condition closes RL verbatim. -/
theorem totalCost_le_rlBudget_of_privatePathCompletion
    {I : Type*} [Fintype I] (cost : I → ℕ)
    (completionOrder s d : ℕ)
    (hGamma : (∑ i : I, cost i) ≤ completionOrder ^ 2)
    (hfit : completionOrder ^ 2 ≤ rlBudget s d) :
    (∑ i : I, cost i) ≤ rlBudget s d :=
  hGamma.trans hfit

#print axioms totalCost_le_rlBudget_of_disjoint_componentResources
#print axioms privatePathOrder_eq_excess_crossTerm
#print axioms cutCondition_of_privatePathPayments
#print axioms privatePathOrder_lt_ambient_of_sq_le_rlBudget
#print axioms totalCost_le_rlBudget_of_privatePathCompletion

end Erdos23QuotientAggregation
