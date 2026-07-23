# Verification protocol

This protocol keeps three claims separate:

1. **Mathematical proof:** the graph-theoretic argument in the paper.
2. **Lean acceptance:** each distributed component compiles without
   placeholders, with its exact theorem boundary documented.
3. **Artifact identity:** the files tested are exactly the files shipped.

Do not infer claim 2 or 3 from claim 1.

## A. Mathematical audit

Check the proof in this order:

- A diametral geodesic is induced, so \(D+1\le b(G)\).
- Every eccentricity is at most \(D\), so
  \(b(G)\le 2+\overline{\mathrm{ecc}}(G)\le D+2\).
- Since \(b(G)\) is integral, \(b(G)=D+1\) or \(b(G)=D+2\).
- In the first case, an outside vertex has two or three consecutive
  neighbors on the diametral path; vertices with the same least
  neighbor index form a clique.
- The order \(v_0,X_0,v_1,\ldots,X_{D-1},v_D\) is Hamiltonian.
- In the second case, equality of average and maximum eccentricity
  makes \(G\) self-centered.
- The standard bound \(b(G)\ge2\operatorname{rad}(G)\) gives \(D\le2\).
- Diameter one contradicts \(b=D+2\); in diameter two the graph has no
  cut vertex.
- \(b\ge\alpha+1\) gives \(\alpha\le3\), and the
  Chvátal–Erdős path theorem applies to the 2-connected graph.

The two imported mathematical results are cited at their theorem
locations in `paper/main.tex`.

## B. Lean audit

The artifact checks the reduction, path-neighborhood classification,
same-index clique lemma, Hamiltonian-path construction, the
self-centered diameter-two connectivity lemma, the longest-path endpoint,
the inequality \(2\operatorname{rad}(G)\le b(G)\), and the exact
`conjecture198a` endpoint.

Run the bundle’s top-level verification script in a fresh checkout or
container. If performing the checks manually, use the exact Lean and
mathlib versions pinned by the included `lean-toolchain` and
`lake-manifest.json`, then run:

```sh
lake update
lake --wfail build
```

The package-level verification script compiles every shipped module in
dependency order against the pinned repository and audits the exact upstream
signature for transitive axioms.

Reject the artifact if any proof placeholder or unreviewed axiom is
present in the submitted development:

```sh
rg -n '\b(sorry|admit)\b|sorryAx|axiom ' --glob '*.lean'
```

Interpret this scan with care: dependencies and comments may contain
these strings. The decisive checks are the source audit and Lean
kernel build, not a grep result alone.

Record:

- `lean --version`
- pinned Formal Conjectures commit
- `git status --short`
- exact build command
- exit status
- start and end timestamps
- SHA-256 of every shipped source and the PDF

## C. PDF audit

Build with `-halt-on-error`, then run:

```sh
pdfinfo main.pdf
pdftotext main.pdf -
pdffonts main.pdf
```

Confirm that:

- all pages render without clipping or overlap;
- mathematical symbols and accents are embedded correctly;
- bibliography references are resolved;
- author and license placeholders have been replaced;
- the artifact-status paragraph agrees with the Lean log.

For visual QA, rasterize every page (for example with `pdftoppm`) and
inspect the resulting images.

## D. Reproducible archive

Generate the ZIP only after the checks above. The final checksum
manifest should be produced from the staged archive contents, not from
similarly named working files. Unpack the ZIP into an empty directory,
run the verification script there, and compare the reported hashes.

Keep `\leanverifiedtrue` in `paper/artifact-status.tex` only while the exact
upstream theorem continues to compile without placeholders or unreviewed
axioms.
