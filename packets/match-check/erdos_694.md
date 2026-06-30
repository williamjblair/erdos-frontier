# Match-check packet — Erdős problem 694

> **Discrepancy** — the frozen AI-contributions wiki records this as a full solution, but the hosted Lean proof is conditional. The resolution decision (L3) at the bottom is the point of this packet.

Computed bucket: `docstring`

## Machine evidence (L1) — deterministic, no human/model judgment

- Verdict: `conditional`
- Non-kernel axioms: `mertens_product, linnik_dvd` (visible to `#print axioms`)

## Wiki claim (frozen AI-contributions wiki, 2026-06-30)

- Recorded outcome: Full solution
- AI systems: Aristotle, Claude Code, Claude Opus 4.7, GPT-5.5 Pro

## 1. Upstream statement

- Boxed problem: https://www.erdosproblems.com/694
- LaTeX source: https://www.erdosproblems.com/latex/694
- Upstream state: `solved (Lean)`

## 2. FC theorem

- File: `FormalConjectures/ErdosProblems/694.lean`
- View: https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/694.lean
- Linked formal_proof: no

## 3. Hosted theorem signature(s)

- plby/lean-proofs — state `conditional` (conditional)
  - https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos694.lean
- Jayyhk/erdos-lean — state `axiomatic` (conditional)
  - https://github.com/Jayyhk/erdos-lean/blob/main/problems/694/Erdos694.lean

## Decision — statement fidelity (L2)

- [ ] faithful — the formal theorem states the boxed problem; safe to link.
- [ ] variant — proves a weaker/variant statement; do not link as complete.
- [ ] unfaithful — does not prove the boxed problem; mismatch.

## Decision — resolution (L3): does the conditional proof justify “formally solved”?

- [ ] solved — the proof is unconditional after all; the machine flag is wrong (if so, clear the problem in `staging_cleared.yaml` only after confirming).
- [ ] conditional — established ONLY under the named assumption; record as conditional, not as a solve.
- [ ] not-solved — the assumption is the crux; this does not resolve the boxed problem.
- [ ] needs-source-update — the boxed problem/answer text needs revision first.
