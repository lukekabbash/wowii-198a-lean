# Prior-solution search record

## Scope and date

A targeted public-record search was completed on 23 July 2026. It covered:

1. the current `google-deepmind/formal-conjectures` statement and its open and
   closed pull requests and issues, searched under `GraphConjecture198a` and
   “Conjecture 198a”;
2. public GitHub code indexed under the exact `GraphConjecture198a`
   identifier;
3. web searches for “Conjecture 198a” together with the graph invariants in
   the statement, the exact Lean identifier, and characteristic phrases from
   the implication; and
4. the original Written on the Wall II source and the two published results
   used in the proof.

The upstream `main` branch was
`e751934294a381afd2d5fc1124c5953c8e25f9fa` at the time of the search. Its
statement remained categorized as `research open` with a `sorry` proof:

<https://github.com/google-deepmind/formal-conjectures/blob/e751934294a381afd2d5fc1124c5953c8e25f9fa/FormalConjectures/WrittenOnTheWallII/GraphConjecture198a.lean>

## Findings

No matching upstream pull request or issue was found. Public GitHub code
search found the upstream statement, benchmark-task copies, and mirrors, but
no public proof source. The exact-phrase web searches likewise produced no
evidence in the searched sources that Conjecture 198a had previously been
solved or formally verified.

The proof uses two published results:

- DeLaViña, Pepper, and Waller, *Independence, Radius and Hamiltonian Paths*,
  MATCH 58 (2007), Theorem 2:
  \(b(G)\ge2\operatorname{rad}(G)\).
  <https://www.uhd.edu/documents/academics/sciences/ind-radius-hamiltonian-pathsdec.pdf>
- Chvátal and Erdős, *A Note on Hamiltonian Circuits*, Discrete Mathematics
  2 (1972), Theorem 2: the path form of the connectivity--independence
  criterion.
  <https://www.renyi.hu/~p_erdos/1972-02.pdf>

## Limitation

This was a targeted deduplication and prior-solution search, not an exhaustive
review of the graph-theory literature. Failure to locate an earlier solution
is negative evidence limited to the sources and queries above; it does not
establish worldwide novelty or priority. No claim of a first proof is made.
