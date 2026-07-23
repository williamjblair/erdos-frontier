# Lean campaign migration index

This is a non-authoritative source index for the open Erdős 23, 617, 699, and
727 campaigns formerly developed in
[`williamjblair/lean-proofs`](https://github.com/williamjblair/lean-proofs).
It preserves exact retrieval paths without copying the repository's generated
working set into this frontier.

This single index supersedes the proposed per-problem `IMPORTED.md` marker
files. Those markers add no provenance beyond the mapping below and are not
needed while the campaign trees remain in pinned Git history.

## Git identities

- Last pre-split source commit:
  `ef1e54ba31563cec6b5169bfc70543a32ac81ef4`.
- Pre-split source tree:
  `7ad702a493246ba7d1ef1b6d49e536cc9df6c98a`.
- Post-split cleanup commit:
  `76d7b563cc98182694e01f1ec7ded90214155a7b`.
- Post-split `lean-proofs` tree:
  `edb78b18d6c37642955e2860e5b4b55ab0434375`. This tree was produced after
  the open campaigns were removed from the active solved-proof library; it is
  not the tree of the pre-split commit.
- Canonical provenance pin already used by this frontier's recovered-attempt
  records: `eab646ceae7f270c024d5d08a8917305b07fd35d`.

The pre-split commit is the retrieval point for later campaign files. The
canonical pin remains the identity of existing recovered records and is not
silently upgraded by this index.

## Problem-to-source map

| Erdős problem | Lean source at the pre-split commit | Supporting source |
| --- | --- | --- |
| 23 | `ErdosProblems/Erdos23*.lean` | `compute23/` |
| 617 | `ErdosProblems/Erdos617.lean` | `compute617/` |
| 699 | `lean/Erdos699.lean` and `lean/Erdos699/` | `PROGRESS_Erdos699.md` and the matching `docs/plans/` records |
| 727 | `ErdosProblems/Erdos727.lean` | none |

These paths identify producer evidence only. They do not make a theorem
accepted, establish statement fidelity, or change any `.vela` state. A future
curation may copy the smallest required source and frozen verifier inputs under
the corresponding `attack/<problem>/` directory, with content hashes and an
explicit replay command.

## License and exclusions

The source repository is MIT licensed (copyright 2026 Will Blair). Any curated
copy must preserve that license and any narrower notice embedded in a source
file.

The bulk working tree is intentionally not imported:

- caches and solver state (`*.pkl`, `*.npz`, `__pycache__/`) are large,
  rebuildable, and environment-dependent;
- compiled binaries are not portable source and must be rebuilt from reviewed
  code;
- PDFs and source archives duplicate material or require a separate asset and
  license review;
- raw logs, dumps, and partial search outputs are activity traces, not frozen
  verifier evidence.

Those files remain retrievable from the pinned Git history. Only a bounded,
content-addressed source or verifier slice should enter this repository.
