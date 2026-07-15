# Statement staging

Drafts from the FC statement campaign live here, one directory per problem.
Nothing in this directory is accepted frontier state. A new draft travels
through the same Receipt v1 and human-sign path as every other claim:

    statements/<n>/
      inputs.md    the drafter's desk: verbatim problem LaTeX, upstream state,
                   hosted theorem extracts with pinned URLs (draft_statement.py)
      <n>.lean     the draft statement in FC house style (drafter edits this)
      draft.json   metadata + divergence notes + collision log
      gates.json   mechanical gate results (gate_draft.sh)

Lifecycle (see campaign.yaml for batch state):

1. `python scripts/draft_statement.py --batch <name>` — stages inputs +
   scaffold; refuses any problem with an open-PR collision.
2. The drafter writes the formal statement from the problem text (hosted
   theorems are a shape prior, never copied blindly) and records every
   divergence in draft.json `divergence_notes`.
3. `bash scripts/gate_draft.sh <n>` — copies into the FC checkout, `lake build`
   (compiles + house linters), extract_names check, link-rule lint.
4. Land the exact Lean file, input packet, `draft.json`, and `gates.json` as
   Receipt v1 artifacts. State explicitly that fidelity to the informal
   problem remains a human judgment.
5. Stop at the routed proposal. A human reviews it with `vela sign`; only the
   exact accepted bytes may be prepared for an outward FC branch.

A drafted `.lean` is never edited after acceptance. Any byte change is a new
artifact and must go through the gate and Receipt path again.
