# Formalization status

## Exact checked endpoint

`lean/src/ConditionalMain.lean` proves `conjecture198a` with the same
arguments and conclusion as the pinned repository statement. The proof
selects a diametral geodesic, establishes
\(b\in\{D+1,D+2\}\), dispatches both branches, and supplies the formally
proved radius--induced-bipartite inequality.

| Component | Lean status |
|---|---|
| \(D+1\le b(G)\), \(\bar e\le D\), and the equality dichotomy | checked |
| Outside-vertex attachment classification in the \(b=D+1\) branch | checked |
| Same-index classes are cliques | checked |
| Clique-block Hamiltonian ordering | checked |
| Eccentricity rigidity in the \(b=D+2\) branch | checked |
| Radius arithmetic reducing to \(D\le2\), assuming \(2r\le b\) | checked |
| One-vertex-deletion connectivity at self-centered diameter two | checked |
| Specialized longest-path theorem for the final traceability step | checked |
| Top-level dispatch of both equality branches | checked |
| Classical graph theorem \(2\operatorname{rad}(G)\le b(G)\) | checked |
| Exact `conjecture198a` endpoint | checked |

All 14 source modules compile with warnings promoted to errors against Lean
4.27.0 and the pinned repository commit. `AxiomAudit.lean` prints the
transitive axioms of the exact public endpoint; the verifier rejects
`sorryAx`, and the captured audit passes.

## Radius-bound proof

`RadiusBipartiteBound.lean` proves \(b(G)\ge2r(G)\) directly. It inducts on
the finite vertex type, deletes a non-cut vertex, and handles the
radius-critical case with two shortest paths. Their induced union either has
at least \(2r\) vertices immediately or has \(2r-1\) vertices; in the latter
case, maximality forces an extension or contradicts the assumed radius.
