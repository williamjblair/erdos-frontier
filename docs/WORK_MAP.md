# Erdős Work Map

This repository is the sole authority for the Erdős research frontier. Other
repositories, commits, proof declarations, computations, and agent runs are
evidence producers. They do not become scientific state merely because they
exist or because a generated map displays them.

## Repository roles

The versioned registry in `sources/work-registry.yaml` assigns every source one
of these roles:

- `authority`: this frontier.
- `federated_theorem_authority`: the pinned Formal Conjectures frontier.
- `artifact_producer`: proof and computation repositories.
- `integration_producer`: the Formal Conjectures integration repository.
- `external_reference`: third-party statements, proofs, and research indexes.
- `deprecated_duplicate`: a historical materialization that must not add to
  counts or state.
- `consumer`: a site or projection that reads published feeds only.

Every public source is pinned by repository identity, commit, selected paths,
and content digest. Dirty worktree overlays are private and are never emitted
into the published feeds.

## Two graph planes

`graph/claim-graph.json` is a canonical projection of replayed findings and
their typed mathematical links. It is truth-bearing only to the extent that
the signed frontier is truth-bearing.

`graph/frontier-map.json` is an operational view. It adds attempts, artifacts,
receipts, verifier attachments, repositories, commits, producers, channels,
leases, and historical records. It is derived navigation data and cannot
establish a claim, proof, or statement-fidelity verdict.

`site/graph.json` remains a compatibility projection during migration. Remove
it only after every maintained consumer reads `graph/frontier-map.json` (or a
root-bound Observatory projection of that file), repository search finds no
remaining consumer, and one released Observatory build has passed exact
node/edge parity without it. Until then it is generated from the canonical map,
never read back as authority.

## Independent status axes

The map does not collapse activity into truth. Each record can carry separate
values for:

- upstream state: `open`, `proved`, or `disproved`;
- activity: attempt, computation, theorem, scout, statement edit, proof-link
  edit, or audit;
- mathematical scope: full, partial, conditional, bounded, variant, or not
  applicable;
- trust: declared, recorded, signed, machine-reproduced, or Lean-attested;
- lifecycle: active, banked, paused, superseded, or historical;
- location: current commit, non-main ref, Git-history-only, or dirty local
  overlay.

The default worked lens is mathematical work. Broader authored-activity counts
include statement and metadata work and must never be described as proof
attempt counts.

## Banking workflow

1. Read the inherited attempts and the root-pinned problem payload.
2. Work in the producer repository, leaving the authority repository free of
   copied source trees.
3. Deposit an attempt with the producer repository, commit, path, digest,
   targeted obligation, methods, obstructions, and remaining obligations.
4. Attach deterministic verification or a draft receipt. Computation output is
   exact-compute evidence, not a proof; Lean evidence is attested only after a
   frozen declaration check succeeds.
5. Submit reusable claims and cross-frontier links as proposals.
6. A key-holding human reviews truth-bearing proposals and statement-fidelity
   judgments. Agents never accept or sign those decisions.
7. Regenerate and double-build the inventory and graph projections.

The legacy importer is dry-run by default. Apply mode is restricted to
`agent:` or `ci:` actors using the agent signing-key mechanism, preserves the
attempt payload, and is idempotent. Its reconciliation report is the audit
surface for every old and new identifier.

## Public and private surfaces

The public feed contains curated summaries, stable repository locators, pinned
commits, digests, signed activity, and accepted state. Raw chats, local absolute
paths, dirty worktrees, unpublished traces, and live agent scratch data belong
only in a private runtime overlay.

The portfolio always contains all 1,217 Erdős problems, including isolated
ones. Every snapshot displays the frontier ID and root so a consumer can say
which exact state it rendered.
