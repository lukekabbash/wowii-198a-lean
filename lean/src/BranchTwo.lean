/- Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0 . -/

import LongestPath
import Proof198a
import RadiusBipartite

/-!
# The `b(G) = diam(G) + 2` branch of WOWII Conjecture 198a

This file joins the numerical radius reduction to the elementary longest-path
theorem in `LongestPath.lean`.  The only external graph-theoretic input is the
radius bound supplied as the hypothesis `hradius`.
-/

namespace WrittenOnTheWallII.GraphConjecture198a

open Classical SimpleGraph

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] [Nontrivial α]

omit [Nontrivial α] in
/--
A finite connected self-centered graph of eccentricity two remains connected
after deleting any one vertex.
-/
theorem simpleGraph_vertexDeletionConnected_of_eccent_eq_two
    (G : SimpleGraph α) (hG : G.Connected)
    (hself : ∀ v : α, G.eccent v = 2) :
    G.VertexDeletionConnected := by
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

/-- A complete graph on a nontrivial finite vertex type satisfies the two
hypotheses of the elementary traceability theorem. -/
lemma exists_hamiltonianPath_completeGraph :
    ∃ a b : α, ∃ p : (⊤ : SimpleGraph α).Walk a b, p.IsHamiltonian := by
  apply SimpleGraph.exists_hamiltonianPath_of_vertexDeletionConnected_of_noIndependentFour
    SimpleGraph.connected_top
  · intro c
    obtain ⟨z, hzc⟩ := exists_ne c
    letI : Nonempty ({c}ᶜ : Set α) :=
      ⟨⟨z, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hzc⟩⟩
    rw [SimpleGraph.induce_top]
    exact SimpleGraph.connected_top
  · intro a b c d hab _hac _had _hbc _hbd _hcd
    exact Or.inl (by simpa using hab)

/--
The hard equality branch of Conjecture 198a.

Assuming the radius--induced-bipartite bound, equality
`bipartiteSize(G) = diam(G) + 2` forces diameter at most two.  Diameter one is
the complete graph.  At diameter two, equality also forces
`indepNum(G) ≤ 3`; self-centeredness gives one-vertex-deletion connectivity,
and the elementary longest-path theorem supplies a Hamiltonian path.
-/
theorem hamiltonianPath_of_bipartiteSize_eq_diam_add_two
    (G : SimpleGraph α) (hG : G.Connected)
    (hb : b G ≤ 2 + averageEccentricity G)
    (hsize :
      largestInducedBipartiteSubgraphSize G = G.diam + 2)
    (hradius :
      2 * G.radius.toNat ≤ largestInducedBipartiteSubgraphSize G) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  have hecc : ∀ v, G.eccent v = (G.diam : ℕ∞) :=
    eccentricity_eq_diam_of_bipartiteSize_eq_diam_add_two G hG hb hsize
  have hdiam : G.diam ≤ 2 :=
    diam_le_two_of_two_mul_radius_le_bipartiteSize
      G hG hecc hsize hradius
  have hdiam_ne : G.diam ≠ 0 :=
    G.connected_iff_diam_ne_zero.mp hG
  have hdiam_cases : G.diam = 1 ∨ G.diam = 2 := by omega
  rcases hdiam_cases with hdiam_one | hdiam_two
  · have htop : G = ⊤ := G.diam_eq_one.mp hdiam_one
    subst G
    exact exists_hamiltonianPath_completeGraph
  · have hself : ∀ v, G.eccent v = 2 := by
      intro v
      simpa [hdiam_two] using hecc v
    have hdelete : G.VertexDeletionConnected :=
      simpleGraph_vertexDeletionConnected_of_eccent_eq_two G hG hself
    have hindep : G.indepNum ≤ 3 := by
      have hα :=
        indepNum_add_one_le_largestInducedBipartiteSubgraphSize G hG
      rw [hsize, hdiam_two] at hα
      omega
    have hfree : G.IndepSetFree 4 := by
      intro s hs
      have hcard := hs.isIndepSet.card_le_indepNum
      rw [hs.card_eq] at hcard
      omega
    exact
      SimpleGraph.exists_hamiltonianPath_of_vertexDeletionConnected_of_noIndependentFour
        hG hdelete (SimpleGraph.noIndependentFour_of_indepSetFree hfree)

end WrittenOnTheWallII.GraphConjecture198a
