/- Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0 . -/

import CaseOneAssembly
import BranchTwo
import RadiusBipartiteBound

/-!
# Completion of WOWII Conjecture 198a

This file joins the two equality branches.  The radius--induced-bipartite
bound used by the `diameter + 2` branch is discharged by
`two_mul_radius_le_largestInducedBipartiteSubgraphSize`.
-/

namespace WrittenOnTheWallII.GraphConjecture198a

open Classical SimpleGraph

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII Conjecture 198a conditional only on the radius--induced-bipartite bound
needed in the `largestInducedBipartiteSubgraphSize = diameter + 2` case.
-/
theorem conjecture198a_of_radius_bipartite_bound
    (G : SimpleGraph α) (hG : G.Connected)
    (hb : b G ≤ 2 + averageEccentricity G)
    (hradius :
      2 * G.radius.toNat ≤ largestInducedBipartiteSubgraphSize G) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  rcases bipartiteSize_eq_diam_add_one_or_two G hG hb with hsize | hsize
  · obtain ⟨u, v, huv⟩ := G.exists_dist_eq_diam
    obtain ⟨p, -, hp⟩ := hG.exists_path_of_dist u v
    have hmax :
        largestInducedBipartiteSubgraphSize G = p.length + 1 := by
      rw [hsize, hp, huv]
    exact
      exists_hamiltonianPath_of_bipartiteSize_eq_geodesic_order p hp hmax
  · exact
      hamiltonianPath_of_bipartiteSize_eq_diam_add_two
        G hG hb hsize hradius

/--
WOWII Conjecture 198a: a finite connected graph satisfying
`b(G) ≤ 2 + averageEccentricity(G)` has a Hamiltonian path.
-/
theorem conjecture198a
    (G : SimpleGraph α) (hG : G.Connected)
    (hb : b G ≤ 2 + averageEccentricity G) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian :=
  conjecture198a_of_radius_bipartite_bound G hG hb
    (two_mul_radius_le_largestInducedBipartiteSubgraphSize G hG)

end WrittenOnTheWallII.GraphConjecture198a
