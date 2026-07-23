/- Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0 . -/

import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Data.Real.Basic
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Induced
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Eccentricity

namespace WrittenOnTheWallII.GraphConjecture198a

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

omit [Fintype α] [Nontrivial α] in
private lemma shortestPath_induce_support_isBipartite
    {G : SimpleGraph α} {u v : α} (p : G.Walk u v)
    (hp : p.length = G.dist u v) :
    (G.induce (p.support.toFinset : Set α)).IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk
    (fun x ↦ ⟨G.dist u x.1 % 2, Nat.mod_lt _ Nat.zero_lt_two⟩) ?_⟩
  intro x y hxy
  have hxy' : G.Adj x.1 y.1 := hxy
  obtain ⟨i, hi, hil⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (by simpa using x.2)
  obtain ⟨j, hj, hjl⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (by simpa using y.2)
  have hdi : G.dist u x.1 = i := by
    rw [← hi]
    have htake :=
      SimpleGraph.length_eq_dist_of_subwalk hp (p.isSubwalk_take i)
    simpa [SimpleGraph.Walk.take_length, Nat.min_eq_left hil] using htake.symm
  have hdj : G.dist u y.1 = j := by
    rw [← hj]
    have htake :=
      SimpleGraph.length_eq_dist_of_subwalk hp (p.isSubwalk_take j)
    simpa [SimpleGraph.Walk.take_length, Nat.min_eq_left hjl] using htake.symm
  have hij : i ≠ j := by
    intro hij
    have : x.1 = y.1 := by
      simpa [hi, hj] using (congrArg p.getVert hij)
    exact hxy'.ne this
  have hadj_dist := hxy'.diff_dist_adj (u := u)
  rw [hdi, hdj] at hadj_dist
  apply Fin.ne_of_val_ne
  change G.dist u x.1 % 2 ≠ G.dist u y.1 % 2
  rw [hdi, hdj]
  intro hmod
  rcases hadj_dist with heq | heq | heq
  · exact hij heq.symm
  · omega
  · omega

omit [DecidableEq α] [Nontrivial α] in
private lemma card_le_largestInducedBipartiteSubgraphSize
    {G : SimpleGraph α} {s : Finset α}
    (hs : (G.induce (s : Set α)).IsBipartite) :
    s.card ≤ largestInducedBipartiteSubgraphSize G := by
  unfold largestInducedBipartiteSubgraphSize
  apply le_csSup
  · refine ⟨Fintype.card α, ?_⟩
    intro n hn
    obtain ⟨t, -, rfl⟩ := hn
    exact t.card_le_univ
  · exact ⟨s, hs, rfl⟩

lemma indepNum_add_one_le_largestInducedBipartiteSubgraphSize
    (G : SimpleGraph α) (hG : G.Connected) :
    G.indepNum + 1 ≤ largestInducedBipartiteSubgraphSize G := by
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  obtain ⟨v⟩ := hG.nonempty
  obtain ⟨w, hvw⟩ := hG.preconnected.exists_adj_of_nontrivial v
  have hedge : s(v, w) ∈ G.edgeSet := by simpa using hvw
  obtain ⟨z, hz⟩ :=
    SimpleGraph.IsIndepSet.nonempty_mem_compl_mem_edge
      G hs.isIndepSet hedge
  have hznot : z ∉ s := by
    rw [Finset.mem_filter] at hz
    simpa using hz.1
  have hbip :
      (G.induce (↑(insert z s) : Set α)).IsBipartite := by
    refine ⟨SimpleGraph.Coloring.mk
      (fun x ↦ if x.1 = z then 0 else 1) ?_⟩
    intro x y hxy
    have hxy' : G.Adj x.1 y.1 := hxy
    by_cases hx : x.1 = z
    · have hy : y.1 ≠ z := by
        intro hy
        exact hxy'.ne (hx.trans hy.symm)
      simp [hx, hy]
    · by_cases hy : y.1 = z
      · simp [hx, hy]
      · exfalso
        have hxs : x.1 ∈ s :=
          (Finset.mem_insert.mp x.2).resolve_left hx
        have hys : y.1 ∈ s :=
          (Finset.mem_insert.mp y.2).resolve_left hy
        exact (hs.isIndepSet hxs hys hxy'.ne) hxy'
  have hcard : (insert z s).card = G.indepNum + 1 := by
    rw [Finset.card_insert_of_notMem hznot, hs.card_eq]
  rw [← hcard]
  exact card_le_largestInducedBipartiteSubgraphSize hbip

lemma diam_add_one_le_b (G : SimpleGraph α) (hG : G.Connected) :
    (G.diam + 1 : ℝ) ≤ b G := by
  obtain ⟨u, v, huv⟩ := G.exists_dist_eq_diam
  obtain ⟨p, hpPath, hpLen⟩ := hG.exists_path_of_dist u v
  have hpLen' : p.length = G.diam := hpLen.trans huv
  have hbip :
      (G.induce (p.support.toFinset : Set α)).IsBipartite :=
    shortestPath_induce_support_isBipartite p hpLen
  have hcard :
      p.support.toFinset.card = G.diam + 1 := by
    rw [List.toFinset_card_of_nodup hpPath.support_nodup,
      SimpleGraph.Walk.length_support, hpLen']
  unfold b
  exact_mod_cast hcard ▸
    card_le_largestInducedBipartiteSubgraphSize hbip

omit [DecidableEq α] in
lemma averageEccentricity_le_diam (G : SimpleGraph α) (hG : G.Connected) :
    averageEccentricity G ≤ G.diam := by
  have htop : G.ediam ≠ ⊤ :=
    G.connected_iff_ediam_ne_top.mp hG
  have hecc (v : α) : (G.eccent v).toNat ≤ G.diam :=
    ENat.toNat_le_toNat eccent_le_ediam htop
  have hcard : (0 : ℝ) < Fintype.card α := by
    exact_mod_cast Fintype.card_pos
  rw [averageEccentricity, div_le_iff₀ hcard]
  norm_cast
  simpa [Finset.card_univ, Nat.mul_comm] using
    Finset.sum_le_sum fun v (_ : v ∈ Finset.univ) ↦ hecc v

lemma bipartiteSize_eq_diam_add_one_or_two
    (G : SimpleGraph α) (hG : G.Connected)
    (hb : b G ≤ 2 + averageEccentricity G) :
    largestInducedBipartiteSubgraphSize G = G.diam + 1 ∨
      largestInducedBipartiteSubgraphSize G = G.diam + 2 := by
  have hloR := diam_add_one_le_b G hG
  have hhiR : b G ≤ (G.diam + 2 : ℝ) := by
    calc
      b G ≤ 2 + averageEccentricity G := hb
      _ ≤ 2 + G.diam := by
        gcongr
        exact averageEccentricity_le_diam G hG
      _ = G.diam + 2 := by ring
  unfold b at hloR hhiR
  have hlo :
      G.diam + 1 ≤ largestInducedBipartiteSubgraphSize G := by
    exact_mod_cast hloR
  have hhi :
      largestInducedBipartiteSubgraphSize G ≤ G.diam + 2 := by
    exact_mod_cast hhiR
  omega

omit [DecidableEq α] in
lemma eccentricity_eq_diam_of_bipartiteSize_eq_diam_add_two
    (G : SimpleGraph α) (hG : G.Connected)
    (hb : b G ≤ 2 + averageEccentricity G)
    (hsize :
      largestInducedBipartiteSubgraphSize G = G.diam + 2) :
    ∀ v, G.eccent v = (G.diam : ℕ∞) := by
  have hb_eq : b G = (G.diam + 2 : ℝ) := by
    unfold b
    exact_mod_cast hsize
  have havg_le := averageEccentricity_le_diam G hG
  have havg_ge : (G.diam : ℝ) ≤ averageEccentricity G := by
    linarith
  have havg : averageEccentricity G = (G.diam : ℝ) :=
    le_antisymm havg_le havg_ge
  have htop : G.ediam ≠ ⊤ :=
    G.connected_iff_ediam_ne_top.mp hG
  have hecc (v : α) : (G.eccent v).toNat ≤ G.diam :=
    ENat.toNat_le_toNat eccent_le_ediam htop
  have hcard : (0 : ℝ) < Fintype.card α := by
    exact_mod_cast Fintype.card_pos
  intro v
  have hnat : (G.eccent v).toNat = G.diam := by
    apply le_antisymm (hecc v)
    by_contra hnot
    have hvlt : (G.eccent v).toNat < G.diam :=
      Nat.lt_of_not_ge hnot
    have hsumlt :
        (∑ x : α, (G.eccent x).toNat) <
          ∑ _x : α, G.diam := by
      apply Finset.sum_lt_sum
      · intro x _
        exact hecc x
      · exact ⟨v, Finset.mem_univ v, hvlt⟩
    have havglt :
        averageEccentricity G < (G.diam : ℝ) := by
      rw [averageEccentricity, div_lt_iff₀ hcard]
      norm_cast
      simpa [Finset.card_univ, Nat.mul_comm] using hsumlt
    exact (ne_of_lt havglt) havg
  have hne : G.eccent v ≠ ⊤ := by
    intro hv
    apply htop
    exact top_unique (hv ▸ eccent_le_ediam)
  calc
    G.eccent v = ((G.eccent v).toNat : ℕ∞) :=
      (ENat.coe_toNat hne).symm
    _ = (G.diam : ℕ∞) := by exact_mod_cast hnat

end WrittenOnTheWallII.GraphConjecture198a
