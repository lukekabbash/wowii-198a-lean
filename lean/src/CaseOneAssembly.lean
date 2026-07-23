/- Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0 . -/

import CaseOneCore
import SameIndexClique
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Range

/-!
# Assembly of the `b = diameter + 1` branch
-/

namespace WrittenOnTheWallII.GraphConjecture198a

open Classical SimpleGraph

/--
The complete `b = diameter + 1` branch.  Vertices outside the geodesic are
grouped by their least path-neighbor index.  The classification and clique
lemmas show that the resulting anchor/block order is Hamiltonian.
-/
theorem exists_hamiltonianPath_of_bipartiteSize_eq_geodesic_order
    {β : Type*} [Fintype β] [DecidableEq β]
    {H : SimpleGraph β} {u v : β} (p : H.Walk u v)
    (hp : p.length = H.dist u v)
    (hmax : largestInducedBipartiteSubgraphSize H = p.length + 1) :
    ∃ a b : β, ∃ q : H.Walk a b, q.IsHamiltonian := by
  let idx : β → ℕ := fun z =>
    if hz : z ∈ p.support then 0
    else Classical.choose
      (geodesic_neighborIndices_eq_pair_or_triple p hp hz hmax)
  have idx_spec (z : β) (hz : z ∉ p.support) :
      idx z < p.length ∧
        (geodesicNeighborIndices p z = {idx z, idx z + 1} ∨
          geodesicNeighborIndices p z = {idx z, idx z + 1, idx z + 2}) := by
    dsimp only [idx]
    rw [dif_neg hz]
    exact Classical.choose_spec
      (geodesic_neighborIndices_eq_pair_or_triple p hp hz hmax)
  let B (j : ℕ) : Finset β :=
    Finset.univ.filter fun z => z ∉ p.support ∧ idx z = j
  let blockAt (j : ℕ) : List β :=
    if j < p.length then (B j).toList else []
  let pairAt (j : ℕ) : β × List β := (p.getVert j, blockAt j)
  let blocks : List (β × List β) :=
    (List.range (p.length + 1)).map pairAt
  let chunkAt (j : ℕ) : List β := p.getVert j :: blockAt j
  have hblock_mem (z : β) (j : ℕ) :
      z ∈ blockAt j ↔ j < p.length ∧ z ∉ p.support ∧ idx z = j := by
    by_cases hj : j < p.length
    · simp [blockAt, hj, B]
    · simp [blockAt, hj]
  have hblock_nodup (j : ℕ) : (blockAt j).Nodup := by
    by_cases hj : j < p.length
    · simpa [blockAt, hj] using (B j).nodup_toList
    · simp [blockAt, hj]
  have hchunk_nodup (j : ℕ) : (chunkAt j).Nodup := by
    change (p.getVert j :: blockAt j).Nodup
    rw [List.nodup_cons]
    constructor
    · intro hmem
      have hout := (hblock_mem (p.getVert j) j).1 hmem |>.2.1
      exact hout (p.getVert_mem_support j)
    · exact hblock_nodup j
  have hchunk_eq (j : ℕ) :
      anchoredChunk (pairAt j) = chunkAt j := by
    rfl
  have hchunks_eq :
      blocks.map anchoredChunk =
        (List.range (p.length + 1)).map chunkAt := by
    simp only [blocks, List.map_map]
    apply congrArg (fun f : ℕ → List β => (List.range (p.length + 1)).map f)
    funext j
    exact hchunk_eq j
  have hclass_of_block {z : β} {j : ℕ} (hz : z ∈ blockAt j) :
      j < p.length ∧ z ∉ p.support ∧ idx z = j ∧
        (geodesicNeighborIndices p z = {j, j + 1} ∨
          geodesicNeighborIndices p z = {j, j + 1, j + 2}) := by
    have hz' := (hblock_mem z j).1 hz
    have hs := idx_spec z hz'.2.1
    rw [hz'.2.2] at hs
    exact ⟨hz'.1, hz'.2.1, hz'.2.2, hs.2⟩
  have hleft_adj {z : β} {j : ℕ} (hz : z ∈ blockAt j) :
      H.Adj (p.getVert j) z := by
    have hc := hclass_of_block hz
    have hm : j ∈ geodesicNeighborIndices p z := by
      rcases hc.2.2.2 with hpair | htriple
      · rw [hpair]
        simp
      · rw [htriple]
        simp
    have hm' := Finset.mem_filter.mp hm
    exact hm'.2.symm
  have hright_adj {z : β} {j : ℕ} (hz : z ∈ blockAt j) :
      H.Adj z (p.getVert (j + 1)) := by
    have hc := hclass_of_block hz
    have hm : j + 1 ∈ geodesicNeighborIndices p z := by
      rcases hc.2.2.2 with hpair | htriple
      · rw [hpair]
        simp
      · rw [htriple]
        simp
    exact (Finset.mem_filter.mp hm).2
  have hblock_clique {j : ℕ} {x y : β}
      (hx : x ∈ blockAt j) (hy : y ∈ blockAt j) (hxy : x ≠ y) :
      H.Adj x y := by
    have hcx := hclass_of_block hx
    have hcy := hclass_of_block hy
    exact same_geodesic_index_adj p hp hcx.2.1 hcy.2.1 hxy hmax j
      hcx.1 hcx.2.2.2 hcy.2.2.2
  have hpair_succ (j : ℕ) (hj : j < p.length) :
      (fun s t : β × List β =>
        H.Adj s.1 t.1 ∧ ∀ z ∈ s.2, H.Adj z t.1)
        (pairAt j) (pairAt (j + 1)) := by
    constructor
    · exact p.adj_getVert_succ hj
    · intro z hz
      exact hright_adj hz
  have hlocal :
      ∀ s ∈ blocks,
        s.2.Nodup ∧
        (∀ z ∈ s.2, H.Adj s.1 z) ∧
        (∀ ⦃x⦄, x ∈ s.2 → ∀ ⦃y⦄, y ∈ s.2 →
          x ≠ y → H.Adj x y) := by
    intro s hs
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hs
    have hjle : j ≤ p.length := by
      simp only [List.mem_range] at hj
      omega
    change
      (blockAt j).Nodup ∧
        (∀ z ∈ blockAt j, H.Adj (p.getVert j) z) ∧
        ∀ ⦃x⦄, x ∈ blockAt j → ∀ ⦃y⦄, y ∈ blockAt j →
          x ≠ y → H.Adj x y
    exact ⟨hblock_nodup j, fun _ => hleft_adj, fun _ hx _ hy => hblock_clique hx hy⟩
  have hsucc :
      blocks.IsChain fun s t =>
        H.Adj s.1 t.1 ∧ ∀ z ∈ s.2, H.Adj z t.1 := by
    change
      ((List.range (p.length + 1)).map pairAt).IsChain fun s t =>
        H.Adj s.1 t.1 ∧ ∀ z ∈ s.2, H.Adj z t.1
    rw [List.isChain_map, List.isChain_range]
    intro j hj
    apply hpair_succ
    omega
  have hpath : p.IsPath := p.isPath_of_length_eq_dist hp
  have hchunk_disjoint (j k : ℕ)
      (hj : j ≤ p.length) (hk : k ≤ p.length) (hjk : j ≠ k) :
      List.Disjoint (chunkAt j) (chunkAt k) := by
    rw [List.disjoint_left]
    intro z hzj hzk
    change z ∈ p.getVert j :: blockAt j at hzj
    change z ∈ p.getVert k :: blockAt k at hzk
    rw [List.mem_cons] at hzj hzk
    rcases hzj with hzj | hzj <;> rcases hzk with hzk | hzk
    · apply hjk
      apply hpath.getVert_injOn
      · simpa only [Set.mem_setOf_eq] using hj
      · simpa only [Set.mem_setOf_eq] using hk
      · exact hzj.symm.trans hzk
    · have hout := (hblock_mem z k).1 hzk |>.2.1
      exact hout (hzj ▸ p.getVert_mem_support j)
    · have hout := (hblock_mem z j).1 hzj |>.2.1
      exact hout (hzk ▸ p.getVert_mem_support k)
    · have hjidx := (hblock_mem z j).1 hzj |>.2.2
      have hkidx := (hblock_mem z k).1 hzk |>.2.2
      exact hjk (hjidx.symm.trans hkidx)
  have hnodup : (blocks.map anchoredChunk).flatten.Nodup := by
    rw [hchunks_eq, List.nodup_flatten]
    constructor
    · intro l hl
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hl
      exact hchunk_nodup j
    · rw [List.pairwise_map]
      have hrange : (List.range (p.length + 1)).Nodup := List.nodup_range
      apply hrange.pairwise_of_forall_ne
      intro j hj k hk hjk
      apply hchunk_disjoint j k
      · simp only [List.mem_range] at hj
        omega
      · simp only [List.mem_range] at hk
        omega
      · exact hjk
  have hcover : ∀ z : β, z ∈ (blocks.map anchoredChunk).flatten := by
    intro z
    rw [hchunks_eq]
    by_cases hz : z ∈ p.support
    · obtain ⟨j, hjvert, hjlen⟩ :=
        SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz
      apply List.mem_flatten.mpr
      refine ⟨chunkAt j, ?_, ?_⟩
      · apply List.mem_map.mpr
        refine ⟨j, ?_, rfl⟩
        simp only [List.mem_range]
        omega
      · change z ∈ p.getVert j :: blockAt j
        rw [List.mem_cons]
        exact Or.inl hjvert.symm
    · have hs := idx_spec z hz
      apply List.mem_flatten.mpr
      refine ⟨chunkAt (idx z), ?_, ?_⟩
      · apply List.mem_map.mpr
        refine ⟨idx z, ?_, rfl⟩
        simp only [List.mem_range]
        omega
      · change z ∈ p.getVert (idx z) :: blockAt (idx z)
        rw [List.mem_cons]
        apply Or.inr
        exact (hblock_mem z (idx z)).2 ⟨hs.1, hz, rfl⟩
  apply has_hamiltonianPath_of_anchored_clique_blocks blocks
  · simp [blocks]
  · exact hlocal
  · exact hsucc
  · exact hnodup
  · exact hcover

end WrittenOnTheWallII.GraphConjecture198a
