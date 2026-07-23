# Verification summary

Environment checked on 23 July 2026:

- Lean 4.27.0;
- Formal Conjectures commit
  `e751934294a381afd2d5fc1124c5953c8e25f9fa`;
- 14 shipped Lean source modules;
- warnings promoted to errors;
- no source proof placeholders;
- transitive axiom audit:
  `propext`, `Classical.choice`, and `Quot.sound` only;
- no `sorryAx` dependency;
- both upstream patch templates pass `git apply --check`;
- LaTeX build has no unresolved references, undefined citations, or overfull
  boxes;
- all PDF fonts are embedded;
- the three-page PDF was rasterized and every page visually inspected;
- a clean temporary PDF rebuild is byte-for-byte reproducible in the checked
  environment.

See `LEAN-VERIFICATION.log` and `PDF-VERIFICATION.txt` for captured output.

This verifies the distributed proof of the exact conjecture, including the
classical inequality \(2\operatorname{rad}(G)\le b(G)\).
