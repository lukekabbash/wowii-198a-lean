#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  printf 'usage: %s /path/to/formal-conjectures\n' "$0" >&2
  exit 2
fi

SCRIPT_DIR="$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)"
REPO_ROOT="$(CDPATH= cd -- "$1" && pwd)"
WORK_DIR="$(mktemp -d "${TMPDIR:-/tmp}/wowii-198a-patches.XXXXXX")"
trap 'rm -rf -- "$WORK_DIR"' EXIT

sed \
  -e 's#<IMMUTABLE_PAPER_URL>#https://example.org/paper#g' \
  "$ROOT_DIR/upstream-pr/GraphConjecture198a-status.patch.in" \
  > "$WORK_DIR/status.patch"

sed \
  -e 's#<IMMUTABLE_PAPER_URL>#https://example.org/paper#g' \
  -e 's#<IMMUTABLE_FORMAL_PROOF_URL>#https://example.org/formal#g' \
  "$ROOT_DIR/upstream-pr/GraphConjecture198a-formal.patch.in" \
  > "$WORK_DIR/formal.patch"

git -C "$REPO_ROOT" apply --check "$WORK_DIR/status.patch"
git -C "$REPO_ROOT" apply --check "$WORK_DIR/formal.patch"
git -C "$REPO_ROOT" apply --check \
  "$ROOT_DIR/upstream-pr/GraphConjecture198a-formal.patch"
printf 'submission patch and templates: PASS\n'
