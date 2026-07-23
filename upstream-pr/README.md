# Upstream PR preparation

Two separate routes are provided, and they must not be conflated:

1. `GraphConjecture198a-formal.patch` is the submission-ready patch. It marks
   the conjecture solved and links the paper and exact Lean theorem at
   immutable URLs.
2. `GraphConjecture198a-status.patch.in` is a fallback template that marks the
   conjecture solved and links only the mathematical paper.
3. `GraphConjecture198a-formal.patch.in` is the reusable formal-proof template.

The submission-ready patch points to artifact commit
`9766921088f9d02017779c63d51133a4aa0c0ba1`.

## Prerequisites

- Rebase or recreate the patch against the current upstream `main`.
- Repeat the dated prior-solution search recorded in
  `notes/PRIOR_SOLUTION_SEARCH.md`.
- Open the required upstream issue, then open the linked non-draft pull
  request without waiting for separate pre-approval.
- Publish the paper at an immutable URL.
- Use the formal-proof route only while the exact upstream theorem compiles
  with no `sorry`, `admit`, `sorryAx`, or new unreviewed axioms.
- Review the repository’s current `AGENTS.md`, contribution guide, and
  formatting requirements.
- Ensure the Google CLA check passes on the pull request.
- Write the issue, pull-request description, review replies, and any Zulip
  message in the contributor's own words.
- Disclose the generative-AI systems used and how they were used. If the
  contribution contains substantial LLM-generated code, add the
  `LLM-generated` label by posting the exact comment `LLM-generated`, as
  required by the current contribution policy.

## Apply the metadata patch

For the submission-ready formal-proof route:

```sh
git apply --check /path/to/GraphConjecture198a-formal.patch
git apply /path/to/GraphConjecture198a-formal.patch
lake --wfail build
```

For the status-only fallback, copy the template and replace the placeholder:

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

## Pull-request description checklist

The contributor should describe the submission in their own words. The
description should cover:

- the exact conjecture and proposed solved status;
- the three mathematical ingredients used in the proof;
- immutable URLs for the paper and exact Lean theorem;
- the Lean version, pinned upstream commit, verification command, and result;
- the scope and limitation of the prior-solution search; and
- the generative-AI systems used and their roles.

Before submission, confirm that the immutable URLs open, the upstream issue is
linked, the current open and closed pull requests have been checked, the full
build passes, and the CLA check is expected to pass.

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
