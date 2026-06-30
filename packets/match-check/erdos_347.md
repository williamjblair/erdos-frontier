# Match-check packet — Erdős problem 347

> **Discrepancy** — the frozen AI-contributions wiki records this as a full solution, but the hosted Lean proof is conditional. The resolution decision (L3) at the bottom is the point of this packet.

Computed bucket: `done`

## Machine evidence (L1) — deterministic, no human/model judgment

- Verdict: `conditional`
- **Undischarged named assumptions** (theorem parameters — `#print axioms` cannot see these):
  - `h : Erdos347.is_cofinite_subsequence S`
  → the proof is conditional on the above; it is NOT an unconditional resolution even if kernel-clean.

## Wiki claim (frozen AI-contributions wiki, 2026-06-30)

- Recorded outcome: Full solution (Lean)
- AI systems: Aristotle, Claude Opus, Codex, GPT
- Humans: Bartosz Naskrecki, Enrique Barschkis, Terence Tao, Wouter van Doorn, jbbaehr22

## 1. Upstream statement

- Boxed problem: https://www.erdosproblems.com/347
- LaTeX source: https://www.erdosproblems.com/latex/347
- Upstream state: `proved (Lean)`

## 2. FC theorem

- File: `FormalConjectures/ErdosProblems/347.lean`
- View: https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/347.lean
- Linked formal_proof: yes

## 3. Hosted theorem signature(s)

- plby/lean-proofs — state `complete` (complete)
  - https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos347.lean
- Jayyhk/erdos-lean — state `complete` (complete)
  - https://github.com/Jayyhk/erdos-lean/blob/main/problems/347/Erdos347.lean

## Decision — statement fidelity (L2)

- [ ] faithful — the formal theorem states the boxed problem; safe to link.
- [ ] variant — proves a weaker/variant statement; do not link as complete.
- [ ] unfaithful — does not prove the boxed problem; mismatch.

## Decision — resolution (L3): does the conditional proof justify “formally solved”?

- [ ] solved — the proof is unconditional after all; the machine flag is wrong (if so, clear the problem in `staging_cleared.yaml` only after confirming).
- [ ] conditional — established ONLY under the named assumption; record as conditional, not as a solve.
- [ ] not-solved — the assumption is the crux; this does not resolve the boxed problem.
- [ ] needs-source-update — the boxed problem/answer text needs revision first.
