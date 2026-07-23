/- Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0 . -/

import PathGeometry
import NeighborhoodArithmetic

/-!
# Exact path-neighborhood classification for the `b = diameter + 1` branch
-/

namespace WrittenOnTheWallII.GraphConjecture198a

open Classical SimpleGraph

/-- Indices on `p` at which the vertex is adjacent to `x`. -/
noncomputable def geodesicNeighborIndices
    {β : Type*} [DecidableEq β] {H : SimpleGraph β}
    {u v : β} (p : H.Walk u v) (x : β) : Finset ℕ :=
  (Finset.range (p.length + 1)).filter fun i => H.Adj x (p.getVert i)

/--
Under the `b = diameter + 1` equality, an outside vertex sees precisely two
or three consecutive vertices of the diametral geodesic.
-/
theorem geodesic_neighborIndices_eq_pair_or_triple
    {β : Type*} [Fintype β] [DecidableEq β]
    {H : SimpleGraph β} {u v x : β} (p : H.Walk u v)
    (hp : p.length = H.dist u v) (hx : x ∉ p.support)
    (hmax : largestInducedBipartiteSubgraphSize H = p.length + 1) :
    ∃ j : ℕ, j < p.length ∧
      (geodesicNeighborIndices p x = {j, j + 1} ∨
        geodesicNeighborIndices p x = {j, j + 1, j + 2}) := by
  let S := geodesicNeighborIndices p x
  have hmem (i : ℕ) :
      i ∈ S ↔ i ≤ p.length ∧ H.Adj x (p.getVert i) := by
    simp [S, geodesicNeighborIndices]
  have hstructure :=
    geodesic_outside_neighbor_parities_and_span p hp hx hmax
  obtain ⟨i0, hi0, hadj0, hpar0⟩ := hstructure.1 (0 : Fin 2)
  obtain ⟨i1, hi1, hadj1, hpar1⟩ := hstructure.1 (1 : Fin 2)
  have hi0S : i0 ∈ S := (hmem i0).2 ⟨hi0, hadj0⟩
  have hi1S : i1 ∈ S := (hmem i1).2 ⟨hi1, hadj1⟩
  have hne : S.Nonempty := ⟨i0, hi0S⟩
  have hspan : ∀ k ∈ S, k ≤ S.min' hne + 2 := by
    intro k hk
    have hk' := (hmem k).1 hk
    have hminS : S.min' hne ∈ S := S.min'_mem hne
    have hmin' := (hmem (S.min' hne)).1 hminS
    exact (hstructure.2 k (S.min' hne) hk'.1 hmin'.1
      hk'.2.symm hmin'.2.symm).1
  have hpar0' : i0 % 2 = 0 := by simpa using hpar0
  have hpar1' : i1 % 2 = 1 := by simpa using hpar1
  have hopp : ∃ k ∈ S, k % 2 ≠ (S.min' hne) % 2 := by
    by_cases hmin0 : (S.min' hne) % 2 = 0
    · exact ⟨i1, hi1S, by omega⟩
    · have hminlt : (S.min' hne) % 2 < 2 :=
        Nat.mod_lt _ Nat.zero_lt_two
      exact ⟨i0, hi0S, by omega⟩
  have hclass :=
    eq_pair_or_triple_of_span_two_and_opposite_parity S hne hspan hopp
  let j := S.min' hne
  have hj1S : j + 1 ∈ S := by
    rcases hclass with hpair | htriple
    · rw [hpair]
      simp [j]
    · rw [htriple]
      simp [j]
  have hjlt : j < p.length := by
    have := (hmem (j + 1)).1 hj1S
    omega
  refine ⟨j, hjlt, ?_⟩
  simpa only [S, j] using hclass

end WrittenOnTheWallII.GraphConjecture198a
