# WOWII Conjecture 198a: checked Lean components

This directory packages the zero-`sorry` Lean components developed for
Written on the Wall II, Conjecture 198a.  They compile against
`google-deepmind/formal-conjectures` at commit
`e751934294a381afd2d5fc1124c5953c8e25f9fa`.

This artifact closes the exact conjecture statement without proof
placeholders.

## Module map

| Module | Local dependencies | Checked contribution |
|---|---|---|
| `Proof198a` | none | A geodesic induces a bipartite graph; `diam + 1 ≤ b`; `averageEccentricity ≤ diam`; the hypothesis forces `b = diam + 1` or `b = diam + 2`; equality in the second case forces every eccentricity to equal the diameter. |
| `PathGeometry` | none | An outside vertex's neighbors on a geodesic span at most two indices; under `b = diam + 1`, both index parities occur. |
| `NeighborhoodArithmetic` | none | Classifies a finite index set of span at most two containing both parities. |
| `CaseOneClassification` | `PathGeometry`, `NeighborhoodArithmetic` | Combines the preceding facts: every outside path-neighborhood consists of two or three consecutive vertices. |
| `SameIndexClique` | `CaseOneClassification` | Proves that two distinct outside vertices with the same least geodesic-neighbor index are adjacent. |
| `CaseOneCore` | none | Turns a duplicate-free adjacency order, chunks, or anchored clique blocks into a Hamiltonian path. |
| `CaseOneAssembly` | `CaseOneCore`, `SameIndexClique` | Completes the `b = diam + 1` branch for a supplied diametral geodesic by grouping outside vertices by their least path-neighbor index and threading the resulting clique blocks. |
| `RadiusBipartite` | none | Identifies radius with diameter in the self-centered branch and proves the arithmetic implication `2 radius ≤ b`, `b = diam + 2` ⇒ `diam ≤ 2`. |
| `RadiusBipartiteBound` | none | Proves `2 * radius ≤ largestInducedBipartiteSubgraphSize` by finite-cardinality induction and an induced-geodesic extremal construction. |
| `SelfCenteredDiameterTwo` | none | Proves that deleting any vertex from a finite connected graph whose eccentricities are all two leaves a connected induced graph. |
| `LongestPath` | none | Gives an elementary longest-path proof that a finite connected graph is traceable if every one-vertex deletion is connected and no four vertices form an independent set. |
| `BranchTwo` | `LongestPath`, `Proof198a`, `RadiusBipartite` | Fully assembles the `b = diam + 2` branch, conditional only on the bound `2 * radius ≤ b`. |
| `ConditionalMain` | `CaseOneAssembly`, `BranchTwo`, `RadiusBipartiteBound` | Proves the exact conjecture; selects a diametral geodesic, dispatches both equality cases, and supplies the verified radius bound. |
| `AxiomAudit` | `ConditionalMain` | Prints the transitive axioms of the exact public endpoint; the verifier rejects any `sorryAx` dependency. |

The only local import edges are:

```text
PathGeometry ───────────┐
                       ├── CaseOneClassification ── SameIndexClique ──┐
NeighborhoodArithmetic ┘                                             ├── CaseOneAssembly
CaseOneCore ──────────────────────────────────────────────────────────┘

LongestPath ───────┐
Proof198a ─────────┼── BranchTwo
RadiusBipartite ───┘

CaseOneAssembly ──┐
BranchTwo ────────┼── ConditionalMain
RadiusBipartiteBound ┘

ConditionalMain ── AxiomAudit
```

## Exact endpoint

`ConditionalMain.conjecture198a` has the same arguments and conclusion as
the pinned upstream theorem. `AxiomAudit` reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Verification

Prepare a clean checkout at the pinned commit, then run:

```sh
git clone https://github.com/google-deepmind/formal-conjectures.git
git -C formal-conjectures checkout --detach e751934294a381afd2d5fc1124c5953c8e25f9fa
./verify.sh ./formal-conjectures
```

The verifier:

1. rejects a different commit or tracked modifications;
2. checks that the packaged source set is exact;
3. scans every source for `sorry`, `admit`, `axiom`, and `proof_wanted`;
4. builds the two required project modules; and
5. compiles every packaged source in dependency order into a temporary
   directory; and
6. audits the public endpoint's transitive axioms and rejects `sorryAx`.

It leaves no `.olean`, toolchain, or dependency cache in this artifact
directory.  Set `LAKE_BIN` when `lake` is not on `PATH`.
