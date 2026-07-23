# Hostile audit: BF-RL aggregation arithmetic and private completion

Status: **partial theorem package, not BF-RL and not a kernel-formalized graph
completion**.

This audit covers
`ErdosProblems/Erdos23GapGBAggregationArithmetic.lean` and the paper
construction in `private_path_completion_findings.md`.

## 1. Dependency tree and per-node verdict

### A. Disjoint component-resource landing

Claim:

```text
∑ resource_i ≤ s and D_i+1 ≤ resource_i for every i
  ⇒ ∑(D_i+1)^2 ≤ rlBudget(s,d).
```

Dependencies: monotonicity of squaring on naturals;
`∑ resource_i^2 ≤ (∑ resource_i)^2`; `s^2 ≤ rlBudget(s,d)`.

Verdict: **kernel checked** as
`totalCost_le_rlBudget_of_disjoint_componentResources`.  The theorem does
not prove that arbitrary graph components meet the displayed hypotheses.
The paper application is limited to demands internal to pairwise distinct
off-corridor components.

### B. Private order identity

Claim:

```text
N_priv = r + ∑(D_i-1) = r + ∑x_i + 3|M|,  D_i=x_i+4.
```

Dependencies: only finite-sum arithmetic.

Verdict: **kernel checked** as `privatePathOrder_eq_excessCrossTerm`.
`privatePathOrder` is a number-valued definition, not a graph constructor.

### C. Cut-payment sum

Claim:

```text
(∀i, mCross_i ≤ pathCross_i)
  ⇒ ∑mCross_i ≤ ∑pathCross_i + extraSupply.
```

Dependencies: finite-sum monotonicity.

Verdict: **kernel checked** as `cutCondition_of_privatePathPayments`.
It does not construct paths, prove they are edge-disjoint, or identify the
summands with graph cut counts.  Those remain paper obligations.

### D. Strict numeric induction gate

Claim:

```text
n=d+1+s,
2s p(d)<(d+1)^2,
N^2≤rlBudget(s,d)
  ⇒ N<n.
```

Dependencies: the definition of `rlBudget` and natural arithmetic.

Verdict: **kernel checked** as
`completionOrder_lt_ambient_of_sq_le_rlBudget`.  It does not establish that
an object of order `N` is a valid Gamma instance.

### E. Final transitivity

Claim:

```text
totalCost ≤ N^2 and N^2 ≤ rlBudget(s,d)
  ⇒ totalCost ≤ rlBudget(s,d).
```

Verdict: **kernel checked** as `totalCost_le_rlBudget_of_completion`.  The
Gamma/induction hypothesis is an explicit premise, not manufactured by the
theorem.

### F. Two-demand convex landing

Claim: for even distances `2A<=2B`, the larger-edge SE2 inequality and

```text
2A+2B <= s+d+p(d)-1
```

imply the exact two-edge RL cost bound throughout the strict BF residual.

Verdict: **kernel checked** as
`twoEvenCosts_le_rlBudget_of_jointDistanceSum`.  The displayed joint sum is
an explicit hypothesis.  No module theorem currently derives it from RFC;
advertising the `|M|=2` graph case as closed before that derivation would be
circular.

The first submitted proof of this node was invalid: its final `nlinarith`
attempt treated the natural variables through their continuous relaxation.
That relaxation is false.  At

```text
s=5, d=9, p(d)=1, A=9/4, B=19/4
```

all relaxed linear hypotheses hold at equality where applicable, but the
pair cost is `281/2`, exceeding `rlBudget(5,9)=135` by `11/2`.  Direct Lean
compilation therefore failed and reported `sorryAx` for the unfinished
theorem.  No cached object from that version is accepted.

The repaired kernel proof has the following dependency nodes:

```text
F0  desired pair cost bound, conditional on the displayed joint sum
 |- F1  d>=3 fixes p(d) from the parity of d
 |- F2  split s mod 2 and d mod 4 (eight exhaustive residue rows)
 |- F3  integrality sharpens both linear caps in each row
 |- F4  convexCorner_scaled: ordered x<=y below a balanced corner (X,Y)
 |- F5  row-wise exact polynomial inequality X^2+Y^2 <= 4 rlBudget
 `- F6  cancel the factor four
```

Per-node verdict: F1--F6 are **kernel checked** inside the same module.  F2
is exhaustive because `s % 2` is zero or one and `d % 4` is zero, one, two,
or three.  F3 is discharged by Presburger arithmetic (`omega`), including
the residue-dependent positive gap between `d` and `2s`.  F4 is proved by
splitting at `2x<=X` and transferring the excess from the smaller coordinate
to the larger one.  F5 uses exact natural multiplication and normalized
quadratic arithmetic.  There is no asymptotic or "essentially" clause.

### G. One distance-four two-demand closure

Claim: if the two costs are `25` and `(2B+1)^2`, the banked SE2 inequality
`4B<=2s+d` for the second edge implies their sum is at most the RL budget in
the strict BF residual.

Verdict: **kernel checked without a joint hypothesis** as
`twoCosts_le_rlBudget_of_oneDistanceFour`.  This is a complete arithmetic
closure of the graph slice once the already-formalized per-edge SE2 theorem
is instantiated.  It does not extend to two distances both at least six.

Here too the discarded one-line continuous proof is false at the boundary:
with `s=5,d=9,B=19/4`, the relaxed cost is `541/4`, exceeding the budget by
`1/4`.  The repaired proof uses the scaled SE2 square bound for `s>=6`; for
`s=5`, the other hypotheses force `d` to be exactly eight or nine and
integrality forces `B<=4`.  Both finite corners are kernel checked.  The
strict-residual hypothesis is not used to manufacture a bound; the proved
arithmetic statement is slightly stronger than its public residual-shaped
surface.

## 2. Independent exact-arithmetic reproduction and integration

`audit_aggregation_arithmetic.py` independently reproduces the two rational
counterexamples, all eight residue rows, the balanced-corner identities, and
the integer conclusions using only Python integers and `Fraction`.  With its
checked default `--max-slack 400`, it reports:

```text
fractional one-four excess: 1/4
fractional pair excess: 11/2
residual frontiers checked: 151454
integer one-four instances covered: 30787343
integer pair instances covered: 2871994078
PASS: residue table and integer landings reproduced exactly
```

For fixed `B`, the pair cost is strictly increasing in `A`; the script checks
the maximal admissible `A` and counts every dominated integer `A` in the last
total.  This finite run is an adversarial reproduction, not the unbounded
proof.  The unbounded claim is supplied only by Lean.

Verification commands run after the repair:

```text
lake env lean ErdosProblems/Erdos23GapGBAggregationArithmetic.lean
lake build ErdosProblems.Erdos23GapGBAggregationArithmetic
bash scripts/check_manifest.sh
```

The direct source check and targeted build exit zero.  Both headline pair
theorems report exactly `[propext, Classical.choice, Quot.sound]`, with no
`sorryAx`.  The module is imported by both `ErdosProblems.lean` and
`Audit.lean`; both public theorems have `axioms_clean: true` entries in
`proofs.yaml`; the manifest/audit comparison passes with 650 tracked
theorems.

## 3. Paper graph-construction obligations

The private-path note proposes a graph with one private path of length
`D_e` for every demand and bridge joins between demand components.  The
following are proved in the paper note and exercised by exact Python tests,
but are **not formalized in Lean**:

1. the finite vertex and edge types and exact order count;
2. simplicity, connectedness, and bipartiteness;
3. the injection from crossing demands to crossing private-path edges;
4. exact preservation `d_H(e)=D_e` for every demand;
5. triangle-freeness of `H ∪ M`;
6. conversion of the strict size gate into an invocation of the precise
   outer Gamma induction hypothesis.

Until all six are kernel checked, the honest status is “paper-level valid
completion plus kernel arithmetic landing,” not “formalized completion.”

## 4. Quantified residual and circularity check

The exact uncovered complement is

```text
(r + ∑_e(D_e-1))^2 > rlBudget(s,d).
```

No theorem in the module bounds the left side, assumes RL on that
complement, or invokes Gamma at the ambient order.  Therefore the package
does not conceal an RL-equivalent lemma or same-order circularity.

## 5. Falsification record

- Long odd cycle: `N_priv=n`; the strict gate correctly does not fire.
- Balanced `C5[q]`: `N_priv=3q^2+2q`; the private construction is
  deliberately noncompetitive and makes no dense-case claim.
- Forced hub and path-packing witnesses: every demand receives private
  capacity.  No per-vertex load or original-graph edge-disjoint routing is
  asserted.
- Mixed series fixture `(D_1,D_2)=(4,6)`: `N_priv=12` and
  `12^2=144≤155`; this is a genuine strict-induction subcase.

All numerical checks use exact integer and Boolean arithmetic in
`test_private_path_completion.py`.  They test the paper construction but do
not raise its Lean formalization status.

The two-demand arithmetic checks additionally use
`audit_aggregation_arithmetic.py`.  In particular, the fractional witnesses
above remain permanently in the audit record so that the failed continuous
proof cannot be reintroduced under a different tactic spelling.
