#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)"
PAPER_DIR="${1:-$ROOT_DIR/paper}"

for command_name in pdfinfo pdffonts pdftotext; do
  if ! command -v "$command_name" >/dev/null 2>&1; then
    printf 'error: required command not found: %s\n' "$command_name" >&2
    exit 1
  fi
done

if command -v latexmk >/dev/null 2>&1; then
  TEX_BUILDER="latexmk"
elif command -v tectonic >/dev/null 2>&1; then
  TEX_BUILDER="tectonic"
else
  printf 'error: required command not found: latexmk or tectonic\n' >&2
  exit 1
fi

if [[ ! -f "$PAPER_DIR/main.tex" ||
      ! -f "$PAPER_DIR/references.bib" ||
      ! -f "$PAPER_DIR/artifact-status.tex" ]]; then
  printf 'error: incomplete paper source directory: %s\n' "$PAPER_DIR" >&2
  exit 1
fi

export SOURCE_DATE_EPOCH=1784795596
export FORCE_SOURCE_DATE=1

(
  cd "$PAPER_DIR"
  if [[ "$TEX_BUILDER" == "latexmk" ]]; then
    latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
  else
    tectonic main.tex --keep-logs --keep-intermediates
  fi
  if command -v rg >/dev/null 2>&1; then
    if rg -n \
      'Overfull|Undefined control sequence|undefined references|Citation .* undefined|Reference .* undefined' \
      main.log; then
      printf 'error: publication-affecting LaTeX warning found\n' >&2
      exit 1
    fi
  fi
  pdfinfo main.pdf
  pdffonts main.pdf
  pdftotext main.pdf - >/dev/null
)

printf 'paper build: PASS (%s/main.pdf)\n' "$PAPER_DIR"
