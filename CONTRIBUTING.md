# Contributing

There are two contribution paths. Both keep activity, verification, and human
judgment separate.

## Contribute a proof upstream

Host the Lean proof in a tracked proof repository or contribute it to Formal
Conjectures. This frontier's audit records the exact repository, commit,
declaration, theorem assumptions, and axiom surface. A clean kernel check is
evidence about the derivation; it is not by itself a judgment that the theorem
faithfully states the informal Erdős problem.

## Land research state through Receipt v1

Install the Vela version declared by [`vela.lock`](vela.lock) (currently
`0.901.0`), clone the frontier, and use the task-first loop:

```bash
vela next . --json
vela work <target> --frontier . --as agent:<your-name> --json

# Produce and verify one bounded artifact, then land it through the session.
vela land --frontier . --work <target> \
  --claim "One scoped result a skeptical reviewer can evaluate." \
  --type theoretical --replayability exact \
  --artifact path/to/result.md:note \
  --caveat "What this result does not establish." \
  --as agent:<your-name> --json
```

A signed policy routes the receipt. Permit admits only a class the human
already delegated, Defer places the exact proposal in the human's sign queue,
and Deny refuses canonical admission. Do not bypass that route by editing
`.vela/`, `frontier.json`, `vela.lock`, or `proof/`.

After landing, commit and push your branch and open a pull request. The Vela
Action replays the event log and checks materialized-state parity. It never
signs or supplies a verdict.

## Formal Conjectures statements

Statement candidates require both mechanical and semantic review:

1. `python scripts/draft_statement.py <n>` gathers pinned inputs and stages the
   candidate.
2. Edit the Lean statement from the verbatim boxed problem text and record
   every divergence from hosted formalizations.
3. `bash scripts/gate_draft.sh <n>` runs the FC build and metadata checks.
4. Land the exact draft and gate record as Receipt v1 artifacts with a caveat
   that statement fidelity remains a human judgment.
5. Stop at the pending proposal. An agent may prepare its key-free Decision
   Plan with `vela review decide . <vpr_id> --accept|--reject --reason <text> --json`;
   only the registered human may approve the protected, root-bound decision
   card. The outward FC branch is prepared only from the exact accepted bytes.

Never add a `formal_proof` link when the machine audit reports a conditional,
axiomatic, partial, or mismatched theorem.

## Verify locally

```bash
vela check .                 # replay, signatures, and parity
vela status . --json
bash scripts/graph.sh build  # deterministic corpus projection
```

`vela check . --strict` additionally treats the catalogue's declared-data
condition debt as release-blocking. That debt is intentionally visible and is
not waived by a non-strict pass.
