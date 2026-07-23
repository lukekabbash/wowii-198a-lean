#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)"

if [[ ! -f "$ROOT_DIR/MANIFEST.sha256" ]]; then
  printf 'error: MANIFEST.sha256 is missing\n' >&2
  exit 1
fi

(
  cd "$ROOT_DIR"
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum --check --strict MANIFEST.sha256
  else
    shasum -a 256 --check MANIFEST.sha256
  fi
)
printf 'manifest: PASS\n'
