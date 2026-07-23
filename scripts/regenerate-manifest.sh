#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)"
TEMP_FILE="$(mktemp "${TMPDIR:-/tmp}/wowii-198a-manifest.XXXXXX")"
trap 'rm -f -- "$TEMP_FILE"' EXIT

(
  cd "$ROOT_DIR"
  FILES="$(
    find . -type f \
    ! -path './MANIFEST.sha256' \
    ! -path './.git/*' \
    ! -path './.DS_Store' \
    ! -path './formal-conjectures/*' \
    ! -path './tmp/*' \
    ! -path './paper/*.aux' \
    ! -path './paper/*.bbl' \
    ! -path './paper/*.blg' \
    ! -path './paper/*.fdb_latexmk' \
    ! -path './paper/*.fls' \
    ! -path './paper/*.log' \
    ! -path './paper/*.out' \
    -print |
    LC_ALL=C sort
  )"
  if command -v sha256sum >/dev/null 2>&1; then
    printf '%s\n' "$FILES" | while IFS= read -r file; do
      sha256sum "$file"
    done
  else
    printf '%s\n' "$FILES" | while IFS= read -r file; do
      shasum -a 256 "$file"
    done
  fi
) > "$TEMP_FILE"

mv -- "$TEMP_FILE" "$ROOT_DIR/MANIFEST.sha256"
trap - EXIT
printf 'manifest regenerated: %s\n' "$ROOT_DIR/MANIFEST.sha256"
