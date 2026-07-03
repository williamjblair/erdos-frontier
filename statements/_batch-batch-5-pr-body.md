Adds Formal Conjectures statements for Erdős problems 71, 206, 209, 328, 353, 403, 426, 464, 512, 621, 639, 648.

Each statement was drafted from the boxed problem text on erdosproblems.com (docstrings verbatim), cross-checked against two independently hosted Lean proofs, and reviewed for statement fidelity before submission. `formal_proof` links (pinned to a commit) are included only where the hosted proof is unconditional under an axiom and hypothesis audit; divergences from the hosted formalizations are noted below.

| problem | upstream state | proof linked | divergence notes |
|---|---|---|---|
| 71 | proved (Lean) | no (statement only) | vs jayyhk: AP encoded with the house predicate Set.IsAPOfLength (⊤ : ℕ∞) on Set ℕ instead of a bespoke InfiniteAP structure; infinite cardinality forces d ≥ 1, so no explicit d_pos field is needed.; … |
| 206 | disproved (Lean) | no (statement only) | vs plby + jayyhk (identical defs in both hosted excerpts): egyptianSum, ValidEgyptian, IsUnderapprox, IsBestNTerm, EventuallyGreedy adopted verbatim; … |
| 209 | disproved (Lean) | no (statement only) | jayyhk states the bare negation `¬ ∀ d, ...`; we use the FC house form for disproved yes/no problems, `answer(False) ↔ ∀ d, ...` (logically equivalent, matches e.g. FC 1128).; … |
| 328 | disproved (Lean) | no (statement only) | Polarity/wrapper: stated as answer(False) ↔ P where P = (∀ C > 0, ∃ t, ∀ A with 1_A∗1_A ≤ C, ∃ partition into t parts each with 1_{A_i}∗1_{A_i} < C) — FC house style for a disproved yes/no question (cf. FC 871, batch-3 333); … |
| 353 | proved (Lean) | no (statement only) | Structure: hosted (jayyhk) packs all five sub-questions into one conjunction theorem erdos_353; draft follows FC house style with headline erdos_353 = the leading isosceles-trapezoid question as answer(True) <-> ..., plus four variants … |
| 403 | proved (Lean) | no (statement only) | jayyhk erdos403_complete/erdos_403 state a complete classification (IsErdos403Solution m s iff the explicit five-solution disjunction); … |
| 426 | disproved (Lean) | no (statement only) | STATEMENT DIRECTION: the drafted theorem states the QUESTION positively as `answer(False) <-> P` (upstream state 'disproved (Lean)' maps to FC category 'research solved' with answer False, per the batch-3 429 precedent); … |
| 464 | proved (Lean) | no (statement only) | vs problem text: the literal conclusion ('{||theta n_k||} is not dense in [0,1]') is vacuously true since ||x|| <= 1/2; formalized instead as the intended content, the sequence (theta n_k) is not dense modulo one: `¬ Dense (Set.range fun k … |
| 512 | proved (Lean) | no (statement only) | jayyhk hosts the statement on `AddCircle (1 : ℝ)` with `haarAddCircle` and the `fourier` monomials; we integrate over θ ∈ [0,1] with `intervalIntegral`, following the problem text's ∫_0^1 literally.; … |
| 621 | proved (Lean) | no (statement only) | vs plby (P4_le_D, P4_add_C4_le_K13): hosted proof works in a bespoke `Trigraph` reformulation and proves inequalities between abstract quantities (P4, C4, D, K13) with no n^2/4 normalization and no alpha_1/tau_1 extremal values; … |
| 639 | proved (Lean) | no (statement only) | Large-n hypothesis: both hosted theorems (plby, jayyhk) witness 'large n' with an explicit `10 <= Fintype.card V`; the draft instead uses the asymptotic form `forall-eventually n in atTop` (FC house style for 'sufficiently large', cf; … |
| 648 | solved (Lean) | yes | range: the draft follows the problem text, 2 <= a_1 < ... < a_t < n (Set.Ico 2 n); both hosted theorems (plby, jayyhk) constrain sequence members to Set.Ioc 0 n, admitting 1 and n and dropping the lower bound 2; … |

For 621, see also #835.

Part of #3998.
