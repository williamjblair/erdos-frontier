# Match-check packet — Erdős problem 1197

> **Discrepancy** — the frozen AI-contributions wiki records this as a full solution, but the hosted Lean proof is conditional. The resolution decision (L3) at the bottom is the point of this packet.

Computed bucket: `docstring`

## Machine evidence (L1) — deterministic, no human/model judgment

- Verdict: `conditional`
- Non-kernel axioms: `Erdos1197.bm_approx_data` (visible to `#print axioms`)

## Wiki claim (frozen AI-contributions wiki, 2026-06-30)

- Recorded outcome: Full solution (Lean)
- AI systems: Aristotle, Claude Opus 4.7, GPT-5.4 Pro

## 1. Upstream statement

- Boxed problem: https://www.erdosproblems.com/1197
- LaTeX source: https://www.erdosproblems.com/latex/1197
- Upstream state: `disproved (Lean)`

## 2. FC theorem

- No Formal Conjectures file for this problem yet.

## 3. Hosted theorem signature(s)

- plby/lean-proofs — state `conditional` (conditional)
  - https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos1197.lean
- Jayyhk/erdos-lean — state `complete` (complete)
  - https://github.com/Jayyhk/erdos-lean/blob/main/problems/1197/Erdos1197.lean

## Decision — statement fidelity (L2)

- [ ] faithful — the formal theorem states the boxed problem; safe to link.
- [ ] variant — proves a weaker/variant statement; do not link as complete.
- [ ] unfaithful — does not prove the boxed problem; mismatch.

## Decision — resolution (L3): does the conditional proof justify “formally solved”?

- [ ] solved — the proof is unconditional after all; the machine flag is wrong (if so, clear the problem in `staging_cleared.yaml` only after confirming).
- [ ] conditional — established ONLY under the named assumption; record as conditional, not as a solve.
- [ ] not-solved — the assumption is the crux; this does not resolve the boxed problem.
- [ ] needs-source-update — the boxed problem/answer text needs revision first.
