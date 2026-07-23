# A Lean 4 proof of WOWII Conjecture 198a

This repository contains a complete mathematical proof of Written on the Wall II,
Conjecture 198a, a concise arXiv-style manuscript, and a substantial Lean 4
formalization checked against `google-deepmind/formal-conjectures` commit
`e751934294a381afd2d5fc1124c5953c8e25f9fa`.

## Result

For every finite nontrivial connected simple graph \(G\),

\[
b(G)\le 2+\overline{\operatorname{ecc}}(G)
\quad\Longrightarrow\quad
G\text{ has a Hamiltonian path}.
\]

The paper proof is complete. The Lean artifact proves the exact conjecture,
including the classical bound
\(2\operatorname{rad}(G)\le b(G)\), with no proof placeholders. The public
endpoint has the same hypotheses and conclusion as the pinned repository
statement.

## Quick verification

Prepare a checkout at the pinned commit:

```sh
git clone https://github.com/google-deepmind/formal-conjectures.git
git -C formal-conjectures checkout --detach \
  e751934294a381afd2d5fc1124c5953c8e25f9fa
./scripts/verify-all.sh ./formal-conjectures
```

The script checks the archive manifest, compiles all shipped Lean modules with
warnings treated as errors, audits the exact endpoint for transitive
`sorryAx` dependence, validates both PR patch templates, and rebuilds and
inspects the PDF in a temporary directory.

## Contents

- `paper/` — LaTeX source, bibliography, metadata, and the verified PDF.
- `lean/` — 14 zero-placeholder Lean source modules and a pinned verifier.
- `notes/` — proof summary, formalization ledger, and prior-solution search
  record.
- `upstream-pr/` — solved-status and formal-proof patch templates and PR
  instructions.
- `verification/` — captured Lean and PDF verification reports.
- `MANIFEST.sha256` — checksums for the staged archive contents.

## Research provenance and generative-AI use disclosure

I used a near-autonomous, iteratively prompted research workflow to identify
and pursue this problem. I began by examining other open problems reported as
solved during the preceding several days, comparing their statements and proof
strategies to assess which nearby conjectures might be approachable. The
resulting model outputs placed this conjecture among comparatively steeper
targets, and I selected it for sustained work.

I then used GPT-5.6 Sol in local Codex at extra-high and ultra reasoning
settings, cloud-hosted ChatGPT work, and individual ChatGPT 5.6 Pro sessions
for iterative research, proof development, Lean formalization, and
verification, continuing until the exact theorem passed the Lean kernel.
GPT-5.6 Sol at extra-high reasoning was used for repository preparation;
Claude Fable 5 and Claude Sonnet 5 were used for limited supplementary
searches.

Model names in the displayed byline and this disclosure identify software
used in the workflow, not independent agency, authorship, or responsibility.
I am the sole human author and take responsibility for the claims and
submitted material. Lean kernel acceptance establishes that the stated proof
terms typecheck in the pinned environment; it does not replace independent
mathematical review.

## Prior-solution search and research status

On 23 July 2026, a targeted search covered the current Formal Conjectures
statement, its open and closed issue and pull-request history, public GitHub
code indexed under the exact theorem identifier, and exact-phrase web
queries. The search found copies of the open conjecture and benchmark tasks,
but no evidence in the searched sources of a proof or verified formalization
predating this work.

This was not an exhaustive literature review. The negative search result does
not establish worldwide novelty or priority, and no “first proof” claim is
made. The search procedure and its limitations are recorded in
`notes/PRIOR_SOLUTION_SEARCH.md`.

## Upstream materials

The proof is intentionally hosted externally because the Formal Conjectures
contribution guide asks that proofs longer than roughly 25–50 lines be linked
through its `formal_proof` mechanism. The tested metadata patch templates and
their verification requirements are in `upstream-pr/`. Any later submission
should use immutable paper and theorem URLs, rerun the dated searches and the
full verifier, and preserve the research-provenance disclosure.

## Licensing

The Lean sources and repository scripts are licensed under Apache-2.0. The
paper and prose documentation are licensed under CC BY 4.0; see
`LICENSE-DOCS.md`.

The manuscript uses an embedded Nimbus Roman Times-family face via
`mathptmx`. Microsoft Times New Roman is proprietary and was not available in
the build environment; Nimbus Roman is the arXiv-compatible redistributable
Times substitute included by standard TeX distributions.
