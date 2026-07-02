#!/usr/bin/env bash
# Sign one statement-faithfulness verdict (`vsa_`) into this frontier — the
# git-native home of the Erdős fidelity frontier (vfr_0a25edabc16db143). It adds
# a finding for the problem and signs the reviewer's verdict on whether the
# Formal Conjectures statement faithfully encodes the informal Erdős problem.
#
# KEY CUSTODY: only a human reviewer can sign. `vela review --fidelity` reserves
# the `vsa_` for `reviewer:` actors and rejects any `agent:` actor — an AI can
# never forge a fidelity judgment. Run this yourself, with your key.
#
# Usage:
#   bash scripts/sign-fidelity.sh <problem> <faithful|variant|unfaithful> "<note>" [--sign]
# Without --sign it prints the plan and writes nothing (safe to preview).
#
# Env: VELA (binary, default `vela`), REVIEWER (default reviewer:will-blair),
#   KEY (private key path, e.g. ~/.vela/keys/will-blair/private.key — or configure
#   `vela id`), FC_DIR (local formal-conjectures checkout used to hash the formal
#   statement bytes; falls back to a zero hash when the file is absent).
#
# After signing, the script materializes the frontier. Commit and push .vela/ +
# frontier.json + vela.lock + proof/ — the "Verify the signed frontier" Action
# re-derives the signed state on push.
set -euo pipefail

VELA="${VELA:-vela}"
REVIEWER="${REVIEWER:-reviewer:will-blair}"
FC_DIR="${FC_DIR:-$HOME/personal/formal-conjectures}"
HERE="$(cd "$(dirname "$0")/.." && pwd)"   # the frontier = repo root

SIGN=0; ARGS=()
for a in "$@"; do [ "$a" = "--sign" ] && SIGN=1 || ARGS+=("$a"); done
N="${ARGS[0]:?problem number required}"
VERDICT="${ARGS[1]:?verdict required (faithful|variant|unfaithful)}"
NOTE="${ARGS[2]:?note required (an attestation without reasoning is a rubber stamp)}"

case "$VERDICT" in faithful|variant|unfaithful) ;; *) echo "verdict must be faithful|variant|unfaithful" >&2; exit 2 ;; esac

FC_FILE="$FC_DIR/FormalConjectures/ErdosProblems/$N.lean"
if [ -f "$FC_FILE" ]; then HASH=$(shasum -a 256 "$FC_FILE" | awk '{print $1}'); else HASH=$(printf '%064d' 0); fi
FORMAL_REF="google-deepmind/formal-conjectures@HEAD:FormalConjectures/ErdosProblems/$N.lean"

echo "problem $N  ->  $VERDICT     (formal_statement_hash ${HASH:0:12}…)"
echo "   reviewer: $REVIEWER"
echo "   note: $NOTE"
if [ "$SIGN" != "1" ]; then
  echo "(dry run — pass --sign to add the finding and sign the verdict with your key)"
  exit 0
fi

KEYARG=(); [ -n "${KEY:-}" ] && KEYARG=(--key "$KEY")

VF=$("$VELA" finding add "$HERE" \
      --assertion "The Formal Conjectures statement for Erdős problem $N faithfully represents the informal problem." \
      --type theoretical --source "erdos-frontier fidelity" \
      --author "$REVIEWER" --apply --json | grep -oE 'vf_[0-9a-f]+' | head -1)
[ -n "$VF" ] || { echo "failed to add finding" >&2; exit 1; }

"$VELA" review "$HERE" "$VF" --fidelity "$VERDICT" \
  --informal-ref "erdosproblems.com/$N" --formal-ref "$FORMAL_REF" \
  --formal-statement-hash "$HASH" --note "$NOTE" --as "$REVIEWER" "${KEYARG[@]}"

echo
echo "signed $N=$VERDICT as $REVIEWER."
echo "(v0.731+: the review verb materialized, committed, and pushed itself —"
echo " decisions self-publish; the Action re-derives the state on the push.)"
