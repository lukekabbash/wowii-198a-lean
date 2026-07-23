# Conjecture 198a paper and PR materials

This directory contains the publication-facing part of a reproducible
solution package for Written on the Wall II, Conjecture 198a.

The central mathematical result is:

> If a finite nontrivial connected simple graph \(G\) satisfies
> \(b(G)\le 2+\overline{\operatorname{ecc}}(G)\), then \(G\) has a
> Hamiltonian path.

The proof is complete on paper. The accompanying zero-placeholder Lean
development kernel-checks the exact repository theorem, including the
classical bound \(b(G)\ge 2\operatorname{rad}(G)\). Consult the final
bundle’s verification log and checksum manifest for the exact environment.

## Contents

- `paper/main.tex` — concise arXiv-style manuscript.
- `paper/references.bib` — bibliography.
- `paper/artifact-status.tex` — explicit verification-status guard.
- `paper/arxiv-metadata.txt` — copy-ready submission metadata with
  authorship, disclosure, and license metadata.
- `VERIFY.md` — clean-build and audit protocol.
- `UPSTREAM_PR.md` — PR checklist and body template.
- `upstream-pr/GraphConjecture198a-status.patch.in` — conservative
  solved-status patch linking the mathematical paper.
- `upstream-pr/GraphConjecture198a-formal.patch.in` — formal-proof metadata
  template, gated on publishing the verified artifact at an immutable URL.

The complete downloadable bundle should also contain the Lean source,
its pinned dependency information, build script, build log, and
checksums. Those are assembled by the package-level tooling outside
this subdirectory.

## Build the paper

From `paper/`, run:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The package-level `scripts/build-paper.sh` also accepts
[Tectonic](https://tectonic-typesetting.github.io/) as a self-contained
fallback. If neither `latexmk` nor Tectonic is available, use:

```sh
pdflatex -interaction=nonstopmode -halt-on-error main.tex
bibtex main
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

The manuscript uses `mathptmx`, a portable Times-family text and
mathematics package available in standard TeX Live and accepted by
arXiv. Microsoft Times New Roman itself is proprietary and is not
bundled here. The visual result follows the requested Times-style
research-paper typography without adding a nonredistributable font.

## Publication and reuse conditions

Any derivative publication or upstream submission should cite the exact
pinned statement, preserve the research-provenance disclosure, use immutable
paper and theorem URLs, and rerun both the clean Lean verification and the
dated prior-solution search. The verified status in
`paper/artifact-status.tex` applies only while the exact theorem remains
closed without placeholders or unreviewed axioms.

The prior-solution search recorded in `notes/PRIOR_SOLUTION_SEARCH.md` found no
evidence in its searched sources of an earlier solution. It was not an
exhaustive literature review and does not establish novelty or priority.
