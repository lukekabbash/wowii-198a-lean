/- Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0 . -/

import Mathlib.Combinatorics.SimpleGraph.Metric
import Lean.Elab.Tactic.Omega
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Induced

/-!
# Geodesic path-neighborhood geometry for WOWII Conjecture 198a
-/

namespace WrittenOnTheWallII.GraphConjecture198a

open Classical SimpleGraph

universe u

variable {α : Type u} {G : SimpleGraph α}

/--
If a vertex is adjacent to the `i`-th and `j`-th vertices of a shortest walk,
with `i ≤ j`, then `j ≤ i + 2`.  Otherwise replacing the portion between
those vertices by the two-edge detour through `x` produces a shorter walk.
-/
theorem neighbor_indices_span_le_two
    {u v x : α} (p : G.Walk u v)
    (hp : p.length = G.dist u v)
    {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length)
    (hix : G.Adj (p.getVert i) x)
    (hxj : G.Adj x (p.getVert j)) :
    j ≤ i + 2 := by
  let q : G.Walk u v :=
    (((p.take i).concat hix).concat hxj).append (p.drop j)
  have hdist := dist_le q
  rw [← hp] at hdist
  simp only [q, Walk.length_append, Walk.length_concat, Walk.take_length,
    Walk.drop_length, Nat.min_eq_left hi] at hdist
  omega

/--
Symmetric form: either index of two neighbors of the same vertex on a shortest
walk is at most two more than the other.
-/
theorem neighbor_indices_span_two_sided
    {u v x : α} (p : G.Walk u v)
    (hp : p.length = G.dist u v)
    {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length)
    (hix : G.Adj (p.getVert i) x)
    (hjx : G.Adj (p.getVert j) x) :
    i ≤ j + 2 ∧ j ≤ i + 2 := by
  constructor
  · exact neighbor_indices_span_le_two p hp hj hi hjx hix.symm
  · exact neighbor_indices_span_le_two p hp hi hj hix hjx.symm

private theorem card_le_largestInducedBipartiteSubgraphSize
    {β : Type*} [Fintype β] [DecidableEq β]
    {H : SimpleGraph β} {s : Finset β}
    (hs : (H.induce (s : Set β)).IsBipartite) :
    s.card ≤ largestInducedBipartiteSubgraphSize H := by
  unfold largestInducedBipartiteSubgraphSize
  apply le_csSup
  · refine ⟨Fintype.card β, ?_⟩
    intro n hn
    obtain ⟨t, -, rfl⟩ := hn
    exact t.card_le_univ
  · exact ⟨s, hs, rfl⟩

/--
If a chosen parity does not occur among the neighbors of `x` on a geodesic,
then adjoining `x` to the geodesic still gives an induced bipartite graph.
-/
theorem insert_geodesic_support_isBipartite_of_missing_parity
    {β : Type*} [Fintype β] [DecidableEq β]
    {H : SimpleGraph β} {u v x : β} (p : H.Walk u v)
    (hp : p.length = H.dist u v)
    (r : Fin 2)
    (hmissing :
      ∀ i : ℕ, i ≤ p.length → H.Adj x (p.getVert i) → i % 2 ≠ r.val) :
    (H.induce
      (insert x p.support.toFinset : Finset β) : SimpleGraph
        {y // y ∈ (insert x p.support.toFinset : Finset β)}).IsBipartite := by
  let color :
      {y // y ∈ (insert x p.support.toFinset : Finset β)} → Fin 2 :=
    fun y =>
      if y.1 = x then r
      else ⟨H.dist u y.1 % 2, Nat.mod_lt _ Nat.zero_lt_two⟩
  refine ⟨SimpleGraph.Coloring.mk color ?_⟩
  intro y z hyz
  have hyz' : H.Adj y.1 z.1 := hyz
  by_cases hy : y.1 = x
  · have hz : z.1 ≠ x := by
      intro hz
      apply hyz'.ne
      exact hy.trans hz.symm
    have hzP : z.1 ∈ p.support := by
      have hzT : z.1 ∈ insert x p.support.toFinset := z.2
      rw [Finset.mem_insert, List.mem_toFinset] at hzT
      exact hzT.resolve_left hz
    obtain ⟨i, hi, hil⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hzP
    have hdi : H.dist u z.1 = i := by
      rw [← hi]
      have htake :=
        SimpleGraph.length_eq_dist_of_subwalk hp (p.isSubwalk_take i)
      simpa [SimpleGraph.Walk.take_length, Nat.min_eq_left hil] using htake.symm
    have hxi : H.Adj x (p.getVert i) := by
      rw [hi]
      simpa only [hy] using hyz'
    intro hcolors
    apply hmissing i hil hxi
    have hvals := congrArg Fin.val hcolors
    simpa [color, hy, hz, hdi] using hvals.symm
  · by_cases hz : z.1 = x
    · have hyP : y.1 ∈ p.support := by
        have hyT : y.1 ∈ insert x p.support.toFinset := y.2
        rw [Finset.mem_insert, List.mem_toFinset] at hyT
        exact hyT.resolve_left hy
      obtain ⟨i, hi, hil⟩ :=
        SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hyP
      have hdi : H.dist u y.1 = i := by
        rw [← hi]
        have htake :=
          SimpleGraph.length_eq_dist_of_subwalk hp (p.isSubwalk_take i)
        simpa [SimpleGraph.Walk.take_length, Nat.min_eq_left hil] using htake.symm
      have hxi : H.Adj x (p.getVert i) := by
        rw [hi]
        simpa only [hz] using hyz'.symm
      intro hcolors
      apply hmissing i hil hxi
      have hvals := congrArg Fin.val hcolors
      simpa [color, hy, hz, hdi] using hvals
    · have hyP : y.1 ∈ p.support := by
        have hyT : y.1 ∈ insert x p.support.toFinset := y.2
        rw [Finset.mem_insert, List.mem_toFinset] at hyT
        exact hyT.resolve_left hy
      have hzP : z.1 ∈ p.support := by
        have hzT : z.1 ∈ insert x p.support.toFinset := z.2
        rw [Finset.mem_insert, List.mem_toFinset] at hzT
        exact hzT.resolve_left hz
      obtain ⟨i, hi, hil⟩ :=
        SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hyP
      obtain ⟨j, hj, hjl⟩ :=
        SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hzP
      have hdi : H.dist u y.1 = i := by
        rw [← hi]
        have htake :=
          SimpleGraph.length_eq_dist_of_subwalk hp (p.isSubwalk_take i)
        simpa [SimpleGraph.Walk.take_length, Nat.min_eq_left hil] using htake.symm
      have hdj : H.dist u z.1 = j := by
        rw [← hj]
        have htake :=
          SimpleGraph.length_eq_dist_of_subwalk hp (p.isSubwalk_take j)
        simpa [SimpleGraph.Walk.take_length, Nat.min_eq_left hjl] using htake.symm
      have hij : i ≠ j := by
        intro hij
        have : y.1 = z.1 := by
          simpa [hi, hj] using congrArg p.getVert hij
        exact hyz'.ne this
      have hadj_dist := hyz'.diff_dist_adj (u := u)
      simp only [hdi, hdj] at hadj_dist
      intro hcolors
      have hvals := congrArg Fin.val hcolors
      simp [color, hy, hz, hdi, hdj] at hvals
      omega

/--
When the maximum induced-bipartite order equals the geodesic order, every
outside vertex has a neighbor of each parity on the geodesic.
-/
theorem exists_geodesic_neighbor_of_each_parity
    {β : Type*} [Fintype β] [DecidableEq β]
    {H : SimpleGraph β} {u v x : β} (p : H.Walk u v)
    (hp : p.length = H.dist u v) (hx : x ∉ p.support)
    (hmax : largestInducedBipartiteSubgraphSize H = p.length + 1) :
    (∀ r : Fin 2,
      ∃ i : ℕ, i ≤ p.length ∧ H.Adj x (p.getVert i) ∧ i % 2 = r.val) := by
  intro r
  by_contra h
  push_neg at h
  have hbip :=
    insert_geodesic_support_isBipartite_of_missing_parity p hp r h
  have hle := card_le_largestInducedBipartiteSubgraphSize hbip
  have hpath : p.IsPath := p.isPath_of_length_eq_dist hp
  have hxfin : x ∉ p.support.toFinset := by simpa using hx
  rw [Finset.card_insert_of_notMem hxfin,
    List.toFinset_card_of_nodup hpath.support_nodup,
    SimpleGraph.Walk.length_support, hmax] at hle
  omega

/--
The first graph-geometry bridge for the `b = diameter + 1` branch: every
outside vertex has path-neighbors of both parities, and all of its
path-neighbor indices lie in an interval of length two.
-/
theorem geodesic_outside_neighbor_parities_and_span
    {β : Type*} [Fintype β] [DecidableEq β]
    {H : SimpleGraph β} {u v x : β} (p : H.Walk u v)
    (hp : p.length = H.dist u v) (hx : x ∉ p.support)
    (hmax : largestInducedBipartiteSubgraphSize H = p.length + 1) :
    (∀ r : Fin 2,
      ∃ i : ℕ, i ≤ p.length ∧ H.Adj x (p.getVert i) ∧ i % 2 = r.val) ∧
    (∀ i j : ℕ, i ≤ p.length → j ≤ p.length →
      H.Adj (p.getVert i) x → H.Adj (p.getVert j) x →
      i ≤ j + 2 ∧ j ≤ i + 2) := by
  constructor
  · exact exists_geodesic_neighbor_of_each_parity p hp hx hmax
  · intro i j hi hj hix hjx
    exact neighbor_indices_span_two_sided p hp hi hj hix hjx

end WrittenOnTheWallII.GraphConjecture198a
