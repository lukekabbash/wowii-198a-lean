# Upstream PR preparation

Two separate routes are provided, and they must not be conflated:

1. `GraphConjecture198a-status.patch.in` marks the conjecture solved and
   links the mathematical paper.
2. `GraphConjecture198a-formal.patch.in` additionally records a
   `formal_proof` URL. Use it after publishing this zero-placeholder exact
   Lean proof at an immutable URL.

## Prerequisites

- Rebase or recreate the patch against the current upstream `main`.
- Repeat the dated prior-solution search recorded in
  `notes/PRIOR_SOLUTION_SEARCH.md`.
- Publish the paper at an immutable URL.
- Ask a maintainer whether a solved-status PR based on a mathematical proof
  is desired.
- Use the formal-proof route only while the exact upstream theorem compiles
  with no `sorry`, `admit`, `sorryAx`, or new unreviewed axioms.
- Review the repository’s current `AGENTS.md`, contribution guide, and
  formatting requirements.
- Sign the Google CLA when prompted.

## Apply the metadata patch

For the current status-only route, copy the template and replace both
placeholders:

```sh
cp upstream-pr/GraphConjecture198a-status.patch.in /tmp/GraphConjecture198a.patch
# Edit <IMMUTABLE_PAPER_URL> in the copy.
git apply --check /tmp/GraphConjecture198a.patch
git apply /tmp/GraphConjecture198a.patch
lake --wfail build
```

Do not submit a `.in` file or an unresolved placeholder.

## Suggested commit

```text
feat(WOWII): mark Conjecture 198a solved
```

## Suggested PR title

```text
feat(WOWII): mark Conjecture 198a solved
```

## PR body template

```markdown
## Summary

Marks Written on the Wall II, Conjecture 198a as solved and links a
mathematical proof at an immutable URL.

The proof uses

1. `diam(G) + 1 ≤ b(G) ≤ 2 + averageEccentricity(G) ≤ diam(G) + 2`;
2. a clique-layer decomposition along a diametral path when
   `b(G) = diam(G) + 1`; and
3. the classical bound `b(G) ≥ 2 * radius(G)` and a self-centered
   diameter-two reduction, followed by the Chvátal–Erdős path theorem,
   when `b(G) = diam(G) + 2`.

## Verification

- Mathematical proof: <IMMUTABLE_PAPER_URL>
- Checked Lean components: <OPTIONAL_IMMUTABLE_ARTIFACT_URL>
- Lean version: 4.27.0
- Base commit: <UPSTREAM_BASE_COMMIT>
- Command: `lake --wfail build`
- Result: pass

## Checklist

- [ ] Paper URL is immutable and opens at the proof
- [ ] Formal-verification claim links the immutable checked artifact
- [ ] Current upstream open and closed PRs checked
- [ ] Formatting and full build pass
- [ ] CLA signed
```

## Gate for the formal-proof template

The accompanying Lean development closes the exact theorem, including
`2 * G.radius.toNat ≤ largestInducedBipartiteSubgraphSize G`. Replace
`<IMMUTABLE_FORMAL_PROOF_URL>` with a published immutable link to the exact
theorem and rerun the full clean build before submission.

## Research-status language

The recorded search found no evidence in its searched sources of an earlier
solution to Conjecture 198a. Because it was not an exhaustive literature
review, it supports neither a “first proof” claim nor a claim of worldwide
novelty or priority. Any upstream summary should preserve that distinction.
