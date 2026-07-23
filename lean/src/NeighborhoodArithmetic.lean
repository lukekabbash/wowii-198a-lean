/- Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0 . -/

import Mathlib.Data.Finset.Max
import Lean.Elab.Tactic.Omega

/-!
# Arithmetic classification of a path-neighborhood

This is the finite arithmetic core used after graph geometry has shown that
the path-neighbor indices of an outside vertex span at most two and include
both parities.
-/

namespace WrittenOnTheWallII.GraphConjecture198a

/--
If a nonempty finite set of natural numbers lies between its minimum `j` and
`j + 2`, and contains an element of parity opposite to `j`, then it is exactly
`{j, j + 1}` or `{j, j + 1, j + 2}`.
-/
theorem eq_pair_or_triple_of_span_two_and_opposite_parity
    (S : Finset ℕ) (hne : S.Nonempty)
    (hspan : ∀ k ∈ S, k ≤ S.min' hne + 2)
    (hopp : ∃ k ∈ S, k % 2 ≠ (S.min' hne) % 2) :
    S = {S.min' hne, S.min' hne + 1} ∨
      S = {S.min' hne, S.min' hne + 1, S.min' hne + 2} := by
  let j := S.min' hne
  change S = {j, j + 1} ∨ S = {j, j + 1, j + 2}
  have hj : j ∈ S := by
    exact S.min'_mem hne
  have hjle : ∀ k ∈ S, j ≤ k := by
    intro k hk
    exact S.min'_le k hk
  obtain ⟨k, hk, hkpar⟩ := hopp
  have hklo := hjle k hk
  have hkhi := hspan k hk
  have hk_eq : k = j + 1 := by
    omega
  have hj1 : j + 1 ∈ S := by
    simpa only [hk_eq] using hk
  by_cases hj2 : j + 2 ∈ S
  · right
    apply Finset.ext
    intro x
    constructor
    · intro hx
      have hxlo := hjle x hx
      have hxhi := hspan x hx
      have hx_cases : x = j ∨ x = j + 1 ∨ x = j + 2 := by
        omega
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hx_cases
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (rfl | rfl | rfl)
      · exact hj
      · exact hj1
      · exact hj2
  · left
    apply Finset.ext
    intro x
    constructor
    · intro hx
      have hxlo := hjle x hx
      have hxhi := hspan x hx
      have hx_cases : x = j ∨ x = j + 1 ∨ x = j + 2 := by
        omega
      rcases hx_cases with rfl | rfl | rfl
      · simp
      · simp
      · exact (hj2 hx).elim
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (rfl | rfl)
      · exact hj
      · exact hj1

end WrittenOnTheWallII.GraphConjecture198a
