/- Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0 . -/

import Mathlib.Combinatorics.SimpleGraph.Diam
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Induced

namespace WrittenOnTheWallII.GraphConjecture198a

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [Nontrivial α]

/-- In the self-centered branch, the (extended) radius is the finite diameter. -/
lemma radius_eq_diam_of_eccentricity_eq_diam
    (G : SimpleGraph α) (hG : G.Connected)
    (hecc : ∀ v, G.eccent v = (G.diam : ℕ∞)) :
    G.radius = (G.diam : ℕ∞) := by
  have hr : G.radius = G.ediam :=
    G.radius_eq_ediam_iff.mpr ⟨(G.diam : ℕ∞), hecc⟩
  have htop : G.ediam ≠ ⊤ :=
    G.connected_iff_ediam_ne_top.mp hG
  calc
    G.radius = G.ediam := hr
    _ = (G.ediam.toNat : ℕ∞) := (ENat.coe_toNat htop).symm
    _ = (G.diam : ℕ∞) := rfl

/--
The numerical final step in the `b = diam + 2` branch.  Its remaining
graph-theoretic input is exactly Fajtlowicz's bound
`2 * radius(G) ≤ b(G)`.
-/
lemma diam_le_two_of_two_mul_radius_le_bipartiteSize
    (G : SimpleGraph α) (hG : G.Connected)
    (hecc : ∀ v, G.eccent v = (G.diam : ℕ∞))
    (hsize :
      largestInducedBipartiteSubgraphSize G = G.diam + 2)
    (hradius :
      2 * G.radius.toNat ≤ largestInducedBipartiteSubgraphSize G) :
    G.diam ≤ 2 := by
  have hr := radius_eq_diam_of_eccentricity_eq_diam G hG hecc
  have hrnat : G.radius.toNat = G.diam := by
    rw [hr]
    simp
  rw [hrnat, hsize] at hradius
  omega

end WrittenOnTheWallII.GraphConjecture198a
