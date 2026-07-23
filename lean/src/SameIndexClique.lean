/- Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0 . -/

import CaseOneClassification

/-!
# The same-index classes are cliques

This is the final structural bridge in the `b = diameter + 1` branch of
WOWII Conjecture 198a.
-/

namespace WrittenOnTheWallII.GraphConjecture198a

open Classical SimpleGraph

private theorem card_le_largestInducedBipartiteSubgraphSize'
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
Two distinct outside vertices with the same least geodesic-neighbor index are
adjacent.  If not, delete the intervening path vertex and add the two outside
vertices; the resulting induced graph has `p.length + 2` vertices and admits
the explicit parity coloring used below.
-/
theorem same_geodesic_index_adj
    {β : Type*} [Fintype β] [DecidableEq β]
    {H : SimpleGraph β} {u v x y : β} (p : H.Walk u v)
    (hp : p.length = H.dist u v)
    (hx : x ∉ p.support) (hy : y ∉ p.support) (hxy : x ≠ y)
    (hmax : largestInducedBipartiteSubgraphSize H = p.length + 1)
    (j : ℕ) (hj : j < p.length)
    (hNx :
      geodesicNeighborIndices p x = {j, j + 1} ∨
        geodesicNeighborIndices p x = {j, j + 1, j + 2})
    (hNy :
      geodesicNeighborIndices p y = {j, j + 1} ∨
        geodesicNeighborIndices p y = {j, j + 1, j + 2}) :
    H.Adj x y := by
  by_contra hnxy
  let mid := p.getVert (j + 1)
  let base := p.support.toFinset.erase mid
  let T := insert x (insert y base)
  have hpath : p.IsPath := p.isPath_of_length_eq_dist hp
  have hmid_support : mid ∈ p.support := by
    exact p.getVert_mem_support (j + 1)
  have hmid_fin : mid ∈ p.support.toFinset := by
    simpa only [List.mem_toFinset] using hmid_support
  have hsupport_card : p.support.toFinset.card = p.length + 1 := by
    rw [List.toFinset_card_of_nodup hpath.support_nodup,
      SimpleGraph.Walk.length_support]
  have hbase_card : base.card = p.length := by
    change (p.support.toFinset.erase mid).card = p.length
    rw [Finset.card_erase_of_mem hmid_fin, hsupport_card]
    omega
  have hxfin : x ∉ p.support.toFinset := by simpa using hx
  have hyfin : y ∉ p.support.toFinset := by simpa using hy
  have hxbase : x ∉ base := by
    simp only [base, Finset.mem_erase, not_and_or]
    exact Or.inr hxfin
  have hybase : y ∉ base := by
    simp only [base, Finset.mem_erase, not_and_or]
    exact Or.inr hyfin
  have hxinsert : x ∉ insert y base := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hxy, hxbase⟩
  have hTcard : T.card = p.length + 2 := by
    change (insert x (insert y base)).card = p.length + 2
    rw [Finset.card_insert_of_notMem hxinsert,
      Finset.card_insert_of_notMem hybase, hbase_card]
  have hindex_mem {z : β} {k : ℕ}
      (hk : k ≤ p.length) (hzk : H.Adj z (p.getVert k)) :
      k ∈ geodesicNeighborIndices p z := by
    simp only [geodesicNeighborIndices, Finset.mem_filter,
      Finset.mem_range]
    constructor
    · omega
    · exact hzk
  have hx_index_cases {k : ℕ}
      (hk : k ≤ p.length) (hxk : H.Adj x (p.getVert k)) :
      k = j ∨ k = j + 1 ∨ k = j + 2 := by
    have hm := hindex_mem hk hxk
    rcases hNx with hpair | htriple
    · rw [hpair] at hm
      have hm' : k = j ∨ k = j + 1 := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
      exact hm'.elim Or.inl fun h => Or.inr (Or.inl h)
    · rw [htriple] at hm
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hy_index_cases {k : ℕ}
      (hk : k ≤ p.length) (hyk : H.Adj y (p.getVert k)) :
      k = j ∨ k = j + 1 ∨ k = j + 2 := by
    have hm := hindex_mem hk hyk
    rcases hNy with hpair | htriple
    · rw [hpair] at hm
      have hm' : k = j ∨ k = j + 1 := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
      exact hm'.elim Or.inl fun h => Or.inr (Or.inl h)
    · rw [htriple] at hm
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hbip :
      (H.induce (T : Set β)).IsBipartite := by
    let special (z : β) : Prop := z = x ∨ z = y
    let color : {z // z ∈ T} → Fin 2 :=
      fun z =>
        if special z.1 then
          ⟨(j + 1) % 2, Nat.mod_lt _ Nat.zero_lt_two⟩
        else
          ⟨H.dist u z.1 % 2, Nat.mod_lt _ Nat.zero_lt_two⟩
    refine ⟨SimpleGraph.Coloring.mk color ?_⟩
    intro a b hab
    have hab' : H.Adj a.1 b.1 := hab
    by_cases ha : special a.1
    · by_cases hb : special b.1
      · rcases ha with haX | haY
        · rcases hb with hbX | hbY
          · exact (hab'.ne (haX.trans hbX.symm)).elim
          · exact (hnxy (by simpa only [haX, hbY] using hab')).elim
        · rcases hb with hbX | hbY
          · exact (hnxy (by simpa only [haY, hbX] using hab'.symm)).elim
          · exact (hab'.ne (haY.trans hbY.symm)).elim
      · have hbneX : b.1 ≠ x := fun h => hb (Or.inl h)
        have hbneY : b.1 ≠ y := fun h => hb (Or.inr h)
        have hbbase : b.1 ∈ base := by
          have hbT : b.1 ∈ T := b.2
          change b.1 ∈ insert x (insert y base) at hbT
          rw [Finset.mem_insert, Finset.mem_insert] at hbT
          rcases hbT with hbx | hby | hbbase
          · exact (hbneX hbx).elim
          · exact (hbneY hby).elim
          · exact hbbase
        have hbbase' := Finset.mem_erase.mp hbbase
        have hbP : b.1 ∈ p.support := by
          simpa only [List.mem_toFinset] using hbbase'.2
        obtain ⟨k, hkvert, hklen⟩ :=
          SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hbP
        have hdb : H.dist u b.1 = k := by
          rw [← hkvert]
          have htake :=
            SimpleGraph.length_eq_dist_of_subwalk hp (p.isSubwalk_take k)
          simpa [SimpleGraph.Walk.take_length, Nat.min_eq_left hklen] using htake.symm
        have hknot : k ≠ j + 1 := by
          intro hk
          apply hbbase'.1
          change b.1 = p.getVert (j + 1)
          rw [← hkvert, hk]
        have hkcases : k = j ∨ k = j + 2 := by
          rcases ha with hax | hay
          · have hxk : H.Adj x (p.getVert k) := by
              rw [hkvert]
              simpa only [hax] using hab'
            rcases hx_index_cases hklen hxk with h | h | h
            · exact Or.inl h
            · exact (hknot h).elim
            · exact Or.inr h
          · have hyk : H.Adj y (p.getVert k) := by
              rw [hkvert]
              simpa only [hay] using hab'
            rcases hy_index_cases hklen hyk with h | h | h
            · exact Or.inl h
            · exact (hknot h).elim
            · exact Or.inr h
        intro hcolors
        have hvals := congrArg Fin.val hcolors
        simp [color, special, ha, hb, hdb] at hvals
        rcases hkcases with rfl | rfl <;> omega
    · by_cases hb : special b.1
      · have haneX : a.1 ≠ x := fun h => ha (Or.inl h)
        have haneY : a.1 ≠ y := fun h => ha (Or.inr h)
        have habase : a.1 ∈ base := by
          have haT : a.1 ∈ T := a.2
          change a.1 ∈ insert x (insert y base) at haT
          rw [Finset.mem_insert, Finset.mem_insert] at haT
          rcases haT with hax | hay | habase
          · exact (haneX hax).elim
          · exact (haneY hay).elim
          · exact habase
        have habase' := Finset.mem_erase.mp habase
        have haP : a.1 ∈ p.support := by
          simpa only [List.mem_toFinset] using habase'.2
        obtain ⟨k, hkvert, hklen⟩ :=
          SimpleGraph.Walk.mem_support_iff_exists_getVert.mp haP
        have hda : H.dist u a.1 = k := by
          rw [← hkvert]
          have htake :=
            SimpleGraph.length_eq_dist_of_subwalk hp (p.isSubwalk_take k)
          simpa [SimpleGraph.Walk.take_length, Nat.min_eq_left hklen] using htake.symm
        have hknot : k ≠ j + 1 := by
          intro hk
          apply habase'.1
          change a.1 = p.getVert (j + 1)
          rw [← hkvert, hk]
        have hkcases : k = j ∨ k = j + 2 := by
          rcases hb with hbx | hby
          · have hxk : H.Adj x (p.getVert k) := by
              rw [hkvert]
              simpa only [hbx] using hab'.symm
            rcases hx_index_cases hklen hxk with h | h | h
            · exact Or.inl h
            · exact (hknot h).elim
            · exact Or.inr h
          · have hyk : H.Adj y (p.getVert k) := by
              rw [hkvert]
              simpa only [hby] using hab'.symm
            rcases hy_index_cases hklen hyk with h | h | h
            · exact Or.inl h
            · exact (hknot h).elim
            · exact Or.inr h
        intro hcolors
        have hvals := congrArg Fin.val hcolors
        simp [color, special, ha, hb, hda] at hvals
        rcases hkcases with rfl | rfl <;> omega
      · have haneX : a.1 ≠ x := fun h => ha (Or.inl h)
        have haneY : a.1 ≠ y := fun h => ha (Or.inr h)
        have hbneX : b.1 ≠ x := fun h => hb (Or.inl h)
        have hbneY : b.1 ≠ y := fun h => hb (Or.inr h)
        have haP : a.1 ∈ p.support := by
          have haT : a.1 ∈ T := a.2
          change a.1 ∈ insert x (insert y base) at haT
          rw [Finset.mem_insert, Finset.mem_insert] at haT
          rcases haT with hax | hay | habase
          · exact (haneX hax).elim
          · exact (haneY hay).elim
          · exact List.mem_toFinset.mp (Finset.mem_erase.mp habase).2
        have hbP : b.1 ∈ p.support := by
          have hbT : b.1 ∈ T := b.2
          change b.1 ∈ insert x (insert y base) at hbT
          rw [Finset.mem_insert, Finset.mem_insert] at hbT
          rcases hbT with hbx | hby | hbbase
          · exact (hbneX hbx).elim
          · exact (hbneY hby).elim
          · exact List.mem_toFinset.mp (Finset.mem_erase.mp hbbase).2
        obtain ⟨k, hkvert, hklen⟩ :=
          SimpleGraph.Walk.mem_support_iff_exists_getVert.mp haP
        obtain ⟨l, hlvert, hllen⟩ :=
          SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hbP
        have hda : H.dist u a.1 = k := by
          rw [← hkvert]
          have htake :=
            SimpleGraph.length_eq_dist_of_subwalk hp (p.isSubwalk_take k)
          simpa [SimpleGraph.Walk.take_length, Nat.min_eq_left hklen] using htake.symm
        have hdb : H.dist u b.1 = l := by
          rw [← hlvert]
          have htake :=
            SimpleGraph.length_eq_dist_of_subwalk hp (p.isSubwalk_take l)
          simpa [SimpleGraph.Walk.take_length, Nat.min_eq_left hllen] using htake.symm
        have hkl : k ≠ l := by
          intro hkl
          have : a.1 = b.1 := by
            simpa [hkvert, hlvert] using congrArg p.getVert hkl
          exact hab'.ne this
        have hadj_dist := hab'.diff_dist_adj (u := u)
        simp only [hda, hdb] at hadj_dist
        intro hcolors
        have hvals := congrArg Fin.val hcolors
        simp [color, special, ha, hb, hda, hdb] at hvals
        omega
  have hle := card_le_largestInducedBipartiteSubgraphSize' hbip
  rw [hTcard, hmax] at hle
  omega

end WrittenOnTheWallII.GraphConjecture198a
