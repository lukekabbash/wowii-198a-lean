#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  printf 'usage: %s /path/to/formal-conjectures\n' "$0" >&2
  exit 2
fi

SCRIPT_DIR="$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)"
REPO_ROOT="$(CDPATH= cd -- "$1" && pwd)"
PAPER_TMP="$(mktemp -d "${TMPDIR:-/tmp}/wowii-198a-paper.XXXXXX")"
trap 'rm -rf -- "$PAPER_TMP"' EXIT

"$SCRIPT_DIR/verify-manifest.sh"
"$ROOT_DIR/lean/verify.sh" "$REPO_ROOT"
"$SCRIPT_DIR/verify-patches.sh" "$REPO_ROOT"

cp "$ROOT_DIR/paper/main.tex" \
   "$ROOT_DIR/paper/references.bib" \
   "$ROOT_DIR/paper/artifact-status.tex" \
   "$PAPER_TMP/"
"$SCRIPT_DIR/build-paper.sh" "$PAPER_TMP"

printf 'full artifact verification: PASS\n'
