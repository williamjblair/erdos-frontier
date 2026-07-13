# Unified Erdős Frontier Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Make `erdos-frontier` the single replayable authority for the complete Erdős research portfolio while keeping proof repositories and agent runs as pinned evidence producers.

**Architecture:** Extend Vela with a dry-run-first, idempotent legacy-attempt importer. In `erdos-frontier`, deterministically inventory pinned repositories, migrate valid activity into signed attempts, and generate separate claim and operational graph projections. Publish a problem-first portfolio and drill-down UI, then make `vela-site` consume the root-pinned feed instead of a baked campaign snapshot.

**Tech Stack:** Rust/Clap/Serde/Vela protocol, Python 3/uv/pytest, generated JSON and static HTML/JavaScript, React/TypeScript/Bun for `vela-site`.

---

### Task 1: Add the Vela attempt importer

**Files:**
- Modify: `vendor/vela/crates/vela-cli/src/server/cli_commands.rs`
- Modify: `vendor/vela/crates/vela-cli/src/tools/cli_lean.rs`
- Test: the colocated Vela CLI/protocol test modules

1. Add failing tests for dry-run, full-field preservation, stable legacy IDs, invalid mappings, apply-mode signing, and idempotent re-import.
2. Add `vela foundry attempt import <ledger> <frontier>` with `--actor`, `--mapping`, `--source-ref`, `--apply`, and `--json`.
3. Require an `agent:` or `ci:` actor and the existing agent signing key in apply mode; never infer verification from `claimed_status`.
4. Emit a complete old-ID/new-ID/action report and skip already-banked attempts without appending events.
5. Run focused Rust tests, then the full Vela conformance suite.

### Task 2: Build the canonical inventory and migration

**Files:**
- Create: `sources/work-registry.yaml`
- Create: `sources/attempt-migration.yaml`
- Create: `scripts/build_work_inventory.py`
- Modify: `sources.lock.json`
- Test: `tests/test_work_inventory.py`

1. Define authority, producer, reference, consumer, and deprecated-duplicate repository roles.
2. Pin remotes, commits, paths, and digests; exclude dirty working-tree data from public output.
3. Account for all 219 legacy records: 212 numbered Erdős attempts, one normalized campaign audit, three OEIS/Sidon records, and three platform-only records.
4. Emit the pinned 102/113/120/248 inventory lenses and the eleven history-only campaigns.
5. Register repository/commit/path/digest locators without copying producer repositories.

### Task 3: Generate the two graph planes

**Files:**
- Modify: `scripts/build_graph.py`
- Create: `graph/claim-graph.json` (generated)
- Create: `graph/frontier-map.json` (generated)
- Create: `site/work-index.json` and per-problem payloads (generated)
- Test: graph schema and semantic regression tests

1. Keep accepted findings and typed mathematical dependencies in the claim graph only.
2. Add attempts, artifacts, receipts, verifiers, repositories, commits, producers, channels, leases, and history to the operational map.
3. Carry source object/event IDs, trust plane, frontier root, evidence locator, and inference status on every operational edge.
4. Preserve `site/graph.json` as a compatibility projection.
5. Prove deterministic double-build output and complete 1,217-problem coverage.

### Task 4: Publish the portfolio and drill-down UI

**Files:**
- Modify: `site/map.html` and generated site assets in `erdos-frontier`
- Modify: the stale Erdős loader/map consumer in `vela-site`
- Test: Python data-contract tests, TypeScript checks, and browser QA

1. Default to one node/card per Erdős problem and the 113-problem mathematical-work lens.
2. Add filters for activity, mathematical scope, trust, lifecycle, repository, and location.
3. Reveal problem-local attempts, obligations, proofs, witnesses, receipts, producers, and commits on selection.
4. Separate activity from accepted state and display the frontier ID/root.
5. Remove the hard-coded 84-work snapshot from `vela-site` and consume the published root-pinned feed.

### Task 5: Reconcile frontiers and establish the operating loop

**Files:**
- Modify: `frontier.yaml`, CI workflows, README/operations documentation
- Read only: `lean-proofs`, `formal-conjectures`, `verified-combinatorics`, and external source mirrors

1. Treat standalone `formal-conjectures-frontier` as canonical and report the nested divergent copy without merging materialized state.
2. Add a pinned cross-frontier dependency and generate proposals for truth-bearing links; do not accept or human-sign them.
3. Document the bank flow: inherit attempts, work in producer repo, deposit root-pinned attempt, attach verification/receipt, submit truth-bearing proposal, regenerate projections.
4. Add CI gates for unlocked sources, duplicate frontier IDs, invalid problem identities, unaccounted records, dirty public provenance, and nondeterministic builds.
5. Run Vela conformance, frontier tests/checks, `vela-site` build gates, and browser QA for #23, #42, #92, #154, #617, #686, and #730.
