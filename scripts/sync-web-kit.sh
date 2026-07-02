#!/usr/bin/env bash
# Sync the vendored Constellate web kit (tokens + frontier-kit + fonts)
# from constellate-science/vela into site/assets/, verbatim.
#
#   scripts/sync-web-kit.sh [ref]     # default: main
#
# Records the synced ref + per-file sha256 in site/assets/KIT_REV so CI
# can prove the vendored copies have not drifted from upstream.
set -euo pipefail

REF="${1:-main}"
RAW="https://raw.githubusercontent.com/constellate-science/vela/${REF}"
DEST="$(cd "$(dirname "$0")/.." && pwd)/site/assets"

FILES=(
  "web/styles/tokens.css:tokens.css"
  "web/styles/frontier-kit.css:frontier-kit.css"
  "web/fonts/inter-latin-400-normal.woff2:fonts/inter-latin-400-normal.woff2"
  "web/fonts/inter-latin-600-normal.woff2:fonts/inter-latin-600-normal.woff2"
  "web/fonts/source-serif-4-latin-400-normal.woff2:fonts/source-serif-4-latin-400-normal.woff2"
  "web/fonts/source-serif-4-latin-400-italic.woff2:fonts/source-serif-4-latin-400-italic.woff2"
  "web/fonts/jetbrains-mono-latin-400-normal.woff2:fonts/jetbrains-mono-latin-400-normal.woff2"
  "web/fonts/LICENSE.md:fonts/LICENSE.md"
)

mkdir -p "$DEST/fonts"
{
  echo "repo: constellate-science/vela"
  echo "ref: ${REF}"
} > "$DEST/KIT_REV"

for spec in "${FILES[@]}"; do
  src="${spec%%:*}"; dst="${spec##*:}"
  curl -fsSL "${RAW}/${src}" -o "$DEST/$dst"
  if command -v sha256sum >/dev/null; then h=$(sha256sum "$DEST/$dst" | cut -d' ' -f1);
  else h=$(shasum -a 256 "$DEST/$dst" | cut -d' ' -f1); fi
  echo "${h}  ${dst}" >> "$DEST/KIT_REV"
  echo "synced ${dst}"
done

echo "kit synced from constellate-science/vela@${REF}"
