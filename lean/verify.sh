#!/usr/bin/env bash
set -euo pipefail

EXPECTED_SHA='e751934294a381afd2d5fc1124c5953c8e25f9fa'

SCRIPT_DIR="$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
SRC_DIR="$SCRIPT_DIR/src"

if [[ $# -ne 1 ]]; then
  printf 'usage: %s /path/to/formal-conjectures\n' "$0" >&2
  exit 2
fi

REPO_ROOT="$(CDPATH= cd -- "$1" && pwd)"

if [[ ! -f "$REPO_ROOT/lakefile.toml" || ! -f "$REPO_ROOT/lean-toolchain" ]]; then
  printf 'error: %s is not a formal-conjectures checkout\n' "$REPO_ROOT" >&2
  exit 1
fi

PIN_FILE_SHA="$(tr -d '[:space:]' < "$SCRIPT_DIR/PINNED_COMMIT")"
if [[ "$PIN_FILE_SHA" != "$EXPECTED_SHA" ]]; then
  printf 'error: PINNED_COMMIT and verify.sh disagree\n' >&2
  exit 1
fi

ACTUAL_SHA="$(git -C "$REPO_ROOT" rev-parse HEAD)"
if [[ "$ACTUAL_SHA" != "$EXPECTED_SHA" ]]; then
  printf 'error: expected commit %s, found %s\n' "$EXPECTED_SHA" "$ACTUAL_SHA" >&2
  exit 1
fi

if ! git -C "$REPO_ROOT" diff --quiet -- ||
   ! git -C "$REPO_ROOT" diff --cached --quiet --; then
  printf 'error: checkout has tracked modifications\n' >&2
  exit 1
fi

EXPECTED_MODULES=(
  AxiomAudit
  BranchTwo
  CaseOneAssembly
  CaseOneClassification
  CaseOneCore
  ConditionalMain
  LongestPath
  NeighborhoodArithmetic
  PathGeometry
  Proof198a
  RadiusBipartite
  RadiusBipartiteBound
  SameIndexClique
  SelfCenteredDiameterTwo
)

ACTUAL_MODULES="$(
  find "$SRC_DIR" -maxdepth 1 -type f -name '*.lean' \
    -exec basename {} .lean \; |
    sort
)"
ACTUAL_MODULE_COUNT="$(
  printf '%s\n' "$ACTUAL_MODULES" |
    awk 'NF { count += 1 } END { print count + 0 }'
)"

if ! diff -u \
    <(printf '%s\n' "${EXPECTED_MODULES[@]}" | sort) \
    <(printf '%s\n' "$ACTUAL_MODULES"); then
  printf 'error: packaged Lean source set differs from the module map\n' >&2
  exit 1
fi

PLACEHOLDER_PATTERN='(^|[^[:alnum:]_])(sorryAx|sorry|admit|axiom|proof_wanted)([^[:alnum:]_]|$)'
if command -v rg >/dev/null 2>&1; then
  if rg -n "$PLACEHOLDER_PATTERN" "$SRC_DIR"/*.lean; then
    printf 'error: proof placeholder found\n' >&2
    exit 1
  fi
else
  if grep -nE "$PLACEHOLDER_PATTERN" "$SRC_DIR"/*.lean; then
    printf 'error: proof placeholder found\n' >&2
    exit 1
  fi
fi
printf 'source scan: PASS (%d modules)\n' "$ACTUAL_MODULE_COUNT"

LAKE_COMMAND="${LAKE_BIN:-lake}"
if [[ "$LAKE_COMMAND" == */* ]]; then
  if [[ "$LAKE_COMMAND" != /* ]]; then
    LAKE_COMMAND="$(CDPATH= cd -- "$(dirname -- "$LAKE_COMMAND")" && pwd)/$(basename -- "$LAKE_COMMAND")"
  fi
elif ! LAKE_COMMAND="$(command -v "$LAKE_COMMAND")"; then
  printf 'error: lake not found; set LAKE_BIN\n' >&2
  exit 1
fi

BUILD_DIR="$(mktemp -d "${TMPDIR:-/tmp}/wowii-198a-lean.XXXXXX")"
trap 'rm -rf -- "$BUILD_DIR"' EXIT
export LEAN_PATH="$BUILD_DIR${LEAN_PATH:+:$LEAN_PATH}"

(
  cd "$REPO_ROOT"
  "$LAKE_COMMAND" build \
    FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Induced \
    FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Eccentricity
)

COMPILE_ORDER=(
  NeighborhoodArithmetic
  PathGeometry
  CaseOneClassification
  SameIndexClique
  CaseOneCore
  CaseOneAssembly
  LongestPath
  Proof198a
  RadiusBipartite
  RadiusBipartiteBound
  SelfCenteredDiameterTwo
  BranchTwo
  ConditionalMain
)

for module in "${COMPILE_ORDER[@]}"; do
  printf 'compiling %s\n' "$module"
  (
    cd "$REPO_ROOT"
    "$LAKE_COMMAND" env lean \
      -DwarningAsError=true \
      -R "$SRC_DIR" \
      -o "$BUILD_DIR/$module.olean" \
      "$SRC_DIR/$module.lean"
  )
done

printf 'auditing transitive axioms\n'
if ! AUDIT_OUTPUT="$(
  cd "$REPO_ROOT"
  "$LAKE_COMMAND" env lean \
    -DwarningAsError=true \
    -R "$SRC_DIR" \
    -o "$BUILD_DIR/AxiomAudit.olean" \
    "$SRC_DIR/AxiomAudit.lean" 2>&1
)"; then
  printf '%s\n' "$AUDIT_OUTPUT" >&2
  exit 1
fi
printf '%s\n' "$AUDIT_OUTPUT"
if [[ "$AUDIT_OUTPUT" == *sorryAx* ]]; then
  printf 'error: public endpoint transitively depends on sorryAx\n' >&2
  exit 1
fi
printf 'axiom audit: PASS (no sorryAx)\n'

printf 'compile: PASS (%d source modules at %s)\n' \
  "$ACTUAL_MODULE_COUNT" "$EXPECTED_SHA"
