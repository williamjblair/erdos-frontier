# erdos-frontier is the canonical Git frontier for Erdős formalization

The architecture follows one product story:

```text
produce -> preserve -> check -> decide -> reuse
```

- Any suitable workbench produces proofs, computations, notes, or Receipt v1
  records. Canopus is optional producer scaffolding.
- This repository preserves content-addressed evidence and canonical frontier
  history in Git.
- Vela replays the history, verifies signatures and roots, and runs declared
  proof or computation checks.
- Signed policy or one protected, proposal-specific human decision controls
  accepted scientific state.
- [Vela Observatory](https://app.vela.space/frontiers/erdos) and other
  replaceable readers support inspection, reproduction, and continued work.

## What the audit establishes

The audit reads each hosted Lean proof of an Erdős problem and reports,
mechanically, whether it establishes the problem outright or only under an
unproven assumption: an axiom it never discharges or a hypothesis it carries.
It cross-references the frozen AI-contributions wiki and the gpt-erdos review,
and keeps separate two questions that a single "solved" mark runs together:

- **Is the proof unconditional?** A fact read from the proof by a declared,
  reproducible check.
- **Is the formal statement the right problem?** A human judgment signed by a
  named reviewer.

The files under `site/`, along with `STATUS.md`, `status.json`, and
`NEXT_BATCH.md`, are generated compatibility views. The Observatory is another
read-only projection. None is the authority boundary.

## Verify the frontier

Judgments live as signed, content-addressed, replayable events in `.vela/`. A
statement-fidelity verdict is a `vsa_` attestation signed by a reviewer and
recorded as an event. Vela replays `frontier.json` and `vela.lock` from that
history:

```bash
git clone https://github.com/vela-science/erdos-frontier
cd erdos-frontier
vela check . --strict     # replays the event log, verifies every signature
```

That command reproduces the materialized state from the events and re-verifies
each signature from the bytes alone. The frontier id is `vfr_0a25edabc16db143`;
no reader is required for this verification.

## What this is not

- Not a claim that a green Lean file is a solved problem: statement fidelity is
  a separate, signed edge.
- Not a place where a model accepts its own results: an agent may draft a
  finding or packet and request one protected decision; it may not approve that
  decision or use a human key.
- Not branding over mechanism: the replay claim above is exactly what
  `vela check` verifies, and no more.

The rule underneath: **tools produce; Git preserves; Vela checks; delegated
policy or a protected human decision decides; replaceable readers enable
reuse.**
