/- Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0 . -/

import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Walks.Maps

namespace WrittenOnTheWallII.GraphConjecture198a

open Classical SimpleGraph

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- Every one-vertex deletion leaves a nonempty connected induced graph. -/
def VertexDeletionConnected (G : SimpleGraph α) : Prop :=
  ∀ c : α, (G.induce ({c}ᶜ : Set α)).Connected

/--
A finite connected self-centered graph of eccentricity two remains connected
after deleting any one vertex.
-/
theorem vertexDeletionConnected_of_eccent_eq_two
    (G : SimpleGraph α) (hG : G.Connected)
    (hself : ∀ v : α, G.eccent v = 2) :
    VertexDeletionConnected G := by
  intro c
  obtain ⟨z, hcz⟩ := G.exists_edist_eq_eccent_of_finite c
  have hcz2 : G.edist c z = 2 := hcz.trans (hself c)
  have hzc : z ≠ c := by
    intro h
    subst z
    simp at hcz2
  have hncz : ¬G.Adj c z := by
    intro h
    have : G.edist c z = 1 := edist_eq_one_iff_adj.mpr h
    rw [this] at hcz2
    simp at hcz2
  let z' : ({c}ᶜ : Set α) := ⟨z, by simpa using hzc⟩
  letI : Nonempty ({c}ᶜ : Set α) := ⟨z'⟩
  refine ⟨?_⟩
  intro u v
  have reach_z (u : ({c}ᶜ : Set α)) :
      (G.induce ({c}ᶜ : Set α)).Reachable u z' := by
    by_cases huz : u.1 = z
    · subst huz
      exact Reachable.rfl
    by_cases hadj : G.Adj u.1 z
    · exact Adj.reachable hadj
    have hedist_le : G.edist u.1 z ≤ 2 := by
      rw [← hself u.1]
      exact edist_le_eccent
    have hdist_le : G.dist u.1 z ≤ 2 := by
      have hcoe : (G.dist u.1 z : ℕ∞) ≤ 2 := by
        rw [(hG u.1 z).coe_dist_eq_edist]
        exact hedist_le
      exact_mod_cast hcoe
    have hdist_gt : 1 < G.dist u.1 z :=
      hG.one_lt_dist_of_ne_of_not_adj huz hadj
    have hdist : G.dist u.1 z = 2 := by omega
    obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist u.1 z
    have hplen : p.length = 2 := hp.trans hdist
    have hpavoid : ∀ x ∈ p.support, x ∈ ({c}ᶜ : Set α) := by
      intro x hx
      obtain ⟨i, hi, hil⟩ :=
        SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
      have hi2 : i ≤ 2 := by omega
      have hicases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases hicases with rfl | rfl | rfl
      · rw [Walk.getVert_zero] at hi
        subst x
        exact u.2
      · have hget2 : p.getVert 2 = z := by
          rw [← hplen]
          exact p.getVert_length
        have hstep : G.Adj (p.getVert 1) (p.getVert 2) :=
          p.adj_getVert_succ (by omega)
        have hstep' : G.Adj x z := by
          simpa only [hi, hget2] using hstep
        change x ≠ c
        intro hxc
        rw [hxc] at hstep'
        exact hncz hstep'
      · have hget2 : p.getVert 2 = z := by
          rw [← hplen]
          exact p.getVert_length
        rw [hget2] at hi
        subst x
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hzc
    exact ⟨p.induce ({c}ᶜ : Set α) hpavoid⟩
  exact (reach_z u).trans (reach_z v).symm

end WrittenOnTheWallII.GraphConjecture198a
