/- Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0 . -/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Walks.Maps
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Induced

/-!
# The radius--induced-bipartite bound

This file proves the classical inequality

`2 * radius(G) ≤ largestInducedBipartiteSubgraphSize(G)`

for finite nontrivial connected simple graphs.  The proof is the standard
non-cut-vertex induction behind the Erdős--Saks--Sós induced-path theorem,
specialized to the bipartite conclusion needed for WOWII Conjecture 198a.
-/

namespace WrittenOnTheWallII.GraphConjecture198a

open Classical SimpleGraph

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
lemma card_le_largestInducedBipartiteSubgraphSize'
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

omit [Fintype α] [DecidableEq α] in
private lemma induced_dist_le
    {G : SimpleGraph α} {s : Set α}
    (hconn : (G.induce s).Connected) (x y : s) :
    G.dist x.1 y.1 ≤ (G.induce s).dist x y := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist x y
  let pm := p.map (Embedding.induce s).toHom
  calc
    G.dist x.1 y.1 ≤ pm.length := G.dist_le pm
    _ = p.length := by
      change (p.map (Embedding.induce s).toHom).length = p.length
      exact Walk.length_map _ _
    _ = (G.induce s).dist x y := hp

omit [DecidableEq α] in
private lemma dist_le_eccent_toNat
    {G : SimpleGraph α} (hG : G.Connected) (x y : α) :
    G.dist x y ≤ (G.eccent x).toNat := by
  letI : Nonempty α := hG.nonempty
  have htop : G.eccent x ≠ ⊤ := by
    have hdtop : G.ediam ≠ ⊤ :=
      G.connected_iff_ediam_ne_top.mp hG
    intro heq
    apply hdtop
    apply top_unique
    simpa [heq] using (eccent_le_ediam (G := G) (u := x))
  exact ENat.toNat_le_toNat G.edist_le_eccent htop

omit [Fintype α] in
private lemma exists_bipartite_pair
    (G : SimpleGraph α) [Nontrivial α] (hG : G.Connected) :
    ∃ s : Finset α,
      (G.induce (s : Set α)).IsBipartite ∧ 2 ≤ s.card := by
  obtain ⟨v⟩ := hG.nonempty
  obtain ⟨w, hvw⟩ := hG.preconnected.exists_adj_of_nontrivial v
  refine ⟨{v, w}, ?_, by simp [hvw.ne]⟩
  refine ⟨SimpleGraph.Coloring.mk (fun x ↦ if x.1 = v then 0 else 1) ?_⟩
  intro x y hxy
  have hxy' : G.Adj x.1 y.1 := hxy
  have hne : x.1 ≠ y.1 := fun h ↦ hxy.ne (Subtype.ext h)
  by_cases hx : x.1 = v
  · have hy : y.1 ≠ v := fun hy ↦ hne (hx.trans hy.symm)
    simp [hx, hy]
  · by_cases hy : y.1 = v
    · simp [hx, hy]
    · have hxw : x.1 = w := by simpa [hx] using x.2
      have hyw : y.1 = w := by simpa [hy] using y.2
      exact (hxy'.ne (hxw.trans hyw.symm)).elim

omit [Fintype α] in
private lemma radius_one_bound
    (G : SimpleGraph α) [Nontrivial α] (hG : G.Connected)
    (hr : G.radius.toNat ≤ 1) :
    ∃ s : Finset α,
      (G.induce (s : Set α)).IsBipartite ∧
        2 * G.radius.toNat ≤ s.card := by
  obtain ⟨s, hs, hcard⟩ := exists_bipartite_pair G hG
  exact ⟨s, hs, by omega⟩

omit [Fintype α] in
private lemma lift_bipartite_from_vertex_deletion
    (G : SimpleGraph α) (v : α)
    {s : Finset ({v}ᶜ : Set α)}
    (hs :
      ((G.induce ({v}ᶜ : Set α)).induce (s : Set ({v}ᶜ : Set α))).IsBipartite) :
    ∃ t : Finset α,
      (G.induce (t : Set α)).IsBipartite ∧ t.card = s.card := by
  let t : Finset α := s.image ((↑) : ({v}ᶜ : Set α) → α)
  have hmem_not (x : {a // a ∈ t}) : x.1 ≠ v := by
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp x.2
    have hyv : y.1 ≠ v := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using y.2
    exact fun hxv ↦ hyv (hxy ▸ hxv)
  let liftVertex (x : {a // a ∈ t}) :
      {y : ({v}ᶜ : Set α) // y ∈ s} :=
    ⟨⟨x.1, by simpa using hmem_not x⟩, by
      obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp x.2
      have heq : y = ⟨x.1, by simpa using hmem_not x⟩ :=
        Subtype.ext hxy
      simpa [heq] using hy⟩
  obtain ⟨C⟩ := hs
  refine ⟨t, ?_, ?_⟩
  · refine ⟨SimpleGraph.Coloring.mk (fun x ↦ C (liftVertex x)) ?_⟩
    intro x y hxy
    apply C.valid
    exact hxy
  · exact Finset.card_image_of_injective s Subtype.val_injective

private lemma almost_bipartite_core_forces_small_radius
    (G : SimpleGraph α) (hG : G.Connected)
    (r : ℕ) (hr : 2 ≤ r)
    (s : Finset α) (c : α) (color : α → Fin 2)
    (hcolor :
      ∀ ⦃x y : α⦄, x ∈ s → y ∈ s → G.Adj x y →
        color x ≠ color y)
    (hcard : s.card = 2 * r - 1)
    (hnear : ∀ x ∈ s, G.dist c x ≤ r - 1)
    (hnear_one :
      ∀ x ∈ s, color x = (1 : Fin 2) → G.dist c x ≤ r - 2)
    (hsmall : largestInducedBipartiteSubgraphSize G < 2 * r) :
    G.radius.toNat < r := by
  have hout (x : α) (hx : x ∉ s) :
      ∃ y ∈ s, color y = (1 : Fin 2) ∧ G.Adj x y := by
    by_contra hn
    push_neg at hn
    have hbip :
        (G.induce (↑(insert x s) : Set α)).IsBipartite := by
      refine ⟨SimpleGraph.Coloring.mk
        (fun z ↦ if z.1 = x then (1 : Fin 2) else color z.1) ?_⟩
      intro a b hab
      have hab' : G.Adj a.1 b.1 := hab
      by_cases ha : a.1 = x
      · have hb : b.1 ≠ x := fun hb ↦ hab'.ne (ha.trans hb.symm)
        have hbs : b.1 ∈ s :=
          (Finset.mem_insert.mp b.2).resolve_left hb
        have hbn : color b.1 ≠ (1 : Fin 2) := by
          have hxb : G.Adj x b.1 := by simpa [ha] using hab'
          exact fun hbeq ↦ hn b.1 hbs hbeq hxb
        simp only [ha, if_pos, hb]
        exact hbn.symm
      · by_cases hb : b.1 = x
        · have has : a.1 ∈ s :=
            (Finset.mem_insert.mp a.2).resolve_left ha
          have han : color a.1 ≠ (1 : Fin 2) := by
            have hxa : G.Adj x a.1 := by simpa [hb] using hab'.symm
            exact fun haeq ↦ hn a.1 has haeq hxa
          simp only [ha, hb, if_pos]
          exact han
        · have has : a.1 ∈ s :=
            (Finset.mem_insert.mp a.2).resolve_left ha
          have hbs : b.1 ∈ s :=
            (Finset.mem_insert.mp b.2).resolve_left hb
          simpa [ha, hb] using hcolor has hbs hab'
    have hle :=
      card_le_largestInducedBipartiteSubgraphSize' hbip
    rw [Finset.card_insert_of_notMem hx, hcard] at hle
    omega
  have hall (x : α) : G.dist c x ≤ r - 1 := by
    by_cases hx : x ∈ s
    · exact hnear x hx
    · obtain ⟨y, hy, hcy, hxy⟩ := hout x hx
      have hdy : G.dist c y ≤ r - 2 := hnear_one y hy hcy
      have htri := hG.dist_triangle (u := c) (v := y) (w := x)
      have hyx : G.dist y x = 1 :=
        dist_eq_one_iff_adj.mpr hxy.symm
      calc
        G.dist c x ≤ G.dist c y + G.dist y x := htri
        _ = G.dist c y + 1 := by rw [hyx]
        _ ≤ (r - 2) + 1 := Nat.add_le_add_right hdy 1
        _ ≤ r - 1 := by omega
  have hecc : G.eccent c ≤ (r - 1 : ℕ∞) := by
    rw [eccent_le_iff]
    intro x
    rw [← (hG c x).coe_dist_eq_edist]
    exact_mod_cast hall x
  have hrad : G.radius ≤ (r - 1 : ℕ∞) :=
    le_trans radius_le_eccent hecc
  have hnat : G.radius.toNat ≤ r - 1 := by
    exact ENat.toNat_le_toNat hrad (by simp)
  omega

omit [Fintype α] [DecidableEq α] in
private lemma geodesic_dist_getVert
    {G : SimpleGraph α} {u v : α} (p : G.Walk u v)
    (hp : p.length = G.dist u v) {i : ℕ} (hi : i ≤ p.length) :
    G.dist u (p.getVert i) = i := by
  have htake :=
    SimpleGraph.length_eq_dist_of_subwalk hp (p.isSubwalk_take i)
  simpa [Walk.take_length, Nat.min_eq_left hi] using htake.symm

omit [Fintype α] [DecidableEq α] in
private lemma geodesic_dist_getVert_getVert
    {G : SimpleGraph α} {u v : α} (p : G.Walk u v)
    (hp : p.length = G.dist u v) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ p.length) :
    G.dist (p.getVert i) (p.getVert j) = j - i := by
  let q := (p.drop i).take (j - i)
  have hsub : q.IsSubwalk p :=
    (Walk.isSubwalk_take (p.drop i) (j - i)).trans
      (Walk.isSubwalk_drop p i)
  have hq := SimpleGraph.length_eq_dist_of_subwalk hp hsub
  have hlen : q.length = j - i := by
    simp [q, Walk.take_length, Walk.drop_length]
    omega
  have hstart : q.getVert 0 = p.getVert i := by simp [q]
  have hend : q.getVert q.length = p.getVert j := by
    simp [q, hlen, Nat.add_sub_of_le hij]
  have hq' :
      G.dist (q.getVert 0) (q.getVert q.length) = q.length := by
    simpa [q, hlen] using hq.symm
  calc
    G.dist (p.getVert i) (p.getVert j) =
        G.dist (q.getVert 0) (q.getVert q.length) := by rw [hstart, hend]
    _ = q.length := hq'
    _ = j - i := hlen

omit [Fintype α] [DecidableEq α] in
private lemma geodesic_adjacent_support_parity
    {G : SimpleGraph α} {u v x y : α} (p : G.Walk u v)
    (hp : p.length = G.dist u v)
    (hx : x ∈ p.support) (hy : y ∈ p.support)
    (hxy : G.Adj x y) :
    G.dist u x % 2 ≠ G.dist u y % 2 := by
  obtain ⟨i, hxi, hi⟩ :=
    Walk.mem_support_iff_exists_getVert.mp hx
  obtain ⟨j, hyj, hj⟩ :=
    Walk.mem_support_iff_exists_getVert.mp hy
  have hdi : G.dist u x = i := by
    rw [← hxi]
    exact geodesic_dist_getVert p hp hi
  have hdj : G.dist u y = j := by
    rw [← hyj]
    exact geodesic_dist_getVert p hp hj
  have hij : i ≠ j := by
    intro hij
    have : x = y := by
      simpa [hxi, hyj] using congrArg p.getVert hij
    exact hxy.ne this
  have hadj := hxy.diff_dist_adj (u := u)
  rw [hdi, hdj] at hadj
  rw [hdi, hdj]
  intro hmod
  rcases hadj with heq | heq | heq
  · exact hij heq.symm
  · omega
  · omega

omit [DecidableEq α] in
private lemma exists_dist_ge_radius
    (G : SimpleGraph α) (hG : G.Connected) (x : α) :
    ∃ y, G.radius.toNat ≤ G.dist x y := by
  letI : Nonempty α := hG.nonempty
  obtain ⟨y, hy⟩ := G.exists_edist_eq_eccent_of_finite x
  refine ⟨y, ?_⟩
  have htop : G.eccent x ≠ ⊤ := by
    have hdtop : G.ediam ≠ ⊤ := G.connected_iff_ediam_ne_top.mp hG
    intro heq
    apply hdtop
    apply top_unique
    simpa [heq] using (eccent_le_ediam (G := G) (u := x))
  have hr := ENat.toNat_le_toNat
    (radius_le_eccent (G := G) (u := x)) htop
  have hdist : G.dist x y = (G.eccent x).toNat := by
    change (G.edist x y).toNat = (G.eccent x).toNat
    rw [hy]
  omega

set_option maxHeartbeats 1000000 in
private lemma critical_case_radius_bipartite
    (G : SimpleGraph α) [Nontrivial α] (hG : G.Connected)
    (r : ℕ) (hr : 2 ≤ r) (hrG : G.radius.toNat = r)
    (vr : α)
    (hdel : (G.induce ({vr}ᶜ : Set α)).Connected)
    (hdelrad : (G.induce ({vr}ᶜ : Set α)).radius.toNat < r) :
    2 * r ≤ largestInducedBipartiteSubgraphSize G := by
  let H := G.induce ({vr}ᶜ : Set α)
  letI : Nonempty ({vr}ᶜ : Set α) := hdel.nonempty
  obtain ⟨v0, hv0⟩ := H.exists_eccent_eq_radius
  change (G.induce ({vr}ᶜ : Set α)).eccent v0 =
    (G.induce ({vr}ᶜ : Set α)).radius at hv0
  have hother (x : α) (hx : x ≠ vr) : G.dist v0.1 x ≤ r - 1 := by
    let xs : ({vr}ᶜ : Set α) := ⟨x, by simpa using hx⟩
    have hdx :
        (G.induce ({vr}ᶜ : Set α)).dist v0 xs ≤
          (G.induce ({vr}ᶜ : Set α)).radius.toNat := by
      rw [← hv0]
      exact dist_le_eccent_toNat hdel v0 xs
    have hlift :
        G.dist v0.1 x ≤ (G.induce ({vr}ᶜ : Set α)).dist v0 xs :=
      induced_dist_le hdel v0 xs
    omega
  have hdvr_le : G.dist v0.1 vr ≤ r := by
    obtain ⟨z, hz⟩ := hG.preconnected.exists_adj_of_nontrivial vr
    have hz_ne : z ≠ vr := hz.ne.symm
    have hzdist : G.dist v0.1 z ≤ r - 1 := hother z hz_ne
    have htri := hG.dist_triangle (u := v0.1) (v := z) (w := vr)
    have hzvr : G.dist z vr = 1 := dist_eq_one_iff_adj.mpr hz.symm
    omega
  have hdvr_ge : r ≤ G.dist v0.1 vr := by
    by_contra hn
    have hdvr : G.dist v0.1 vr ≤ r - 1 := by omega
    have hall (x : α) : G.dist v0.1 x ≤ r - 1 := by
      by_cases hx : x = vr
      · simpa [hx] using hdvr
      · exact hother x hx
    have hecc : G.eccent v0.1 ≤ (r - 1 : ℕ∞) := by
      rw [eccent_le_iff]
      intro x
      rw [← (hG v0.1 x).coe_dist_eq_edist]
      exact_mod_cast hall x
    have hrad : G.radius ≤ (r - 1 : ℕ∞) :=
      le_trans radius_le_eccent hecc
    have hnat : G.radius.toNat ≤ r - 1 :=
      ENat.toNat_le_toNat hrad (by simp)
    omega
  have hdvr : G.dist v0.1 vr = r := le_antisymm hdvr_le hdvr_ge
  obtain ⟨q, hqpath, hqlen⟩ := hG.exists_path_of_dist v0.1 vr
  have hqlenr : q.length = r := hqlen.trans hdvr
  let v1 := q.getVert 1
  let v2 := q.getVert 2
  have h1le : 1 ≤ q.length := by omega
  have h2le : 2 ≤ q.length := by omega
  obtain ⟨w, hwfar⟩ := exists_dist_ge_radius G hG v2
  have hv2vr : G.dist v2 vr = r - 2 := by
    calc
      G.dist v2 vr =
          G.dist (q.getVert 2) (q.getVert q.length) := by simp [v2]
      _ = q.length - 2 :=
        geodesic_dist_getVert_getVert q hqlen
          (show 2 ≤ q.length by omega) (le_refl q.length)
      _ = r - 2 := by rw [hqlenr]
  have hwne : w ≠ vr := by
    intro h
    subst w
    rw [hrG, hv2vr] at hwfar
    omega
  have hv0w_le : G.dist v0.1 w ≤ r - 1 := hother w hwne
  obtain ⟨p, hppath, hplen⟩ := hG.exists_path_of_dist v0.1 w
  have hp_upper : p.length ≤ r - 1 := by omega
  have hv0v2 : G.dist v0.1 v2 = 2 := by
    simpa [v2] using geodesic_dist_getVert q hqlen h2le
  have hp_lower : r - 2 ≤ p.length := by
    have htri := hG.dist_triangle (u := v2) (v := v0.1) (w := w)
    have hv2v0 : G.dist v2 v0.1 = 2 := by
      rw [dist_comm]
      exact hv0v2
    rw [hv2v0, ← hplen] at htri
    rw [hrG] at hwfar
    omega
  have hp_cases : p.length = r - 2 ∨ p.length = r - 1 := by omega
  have hp_position (x : α) (hx : x ∈ p.support) :
      ∃ i : ℕ, i ≤ p.length ∧ p.getVert i = x ∧
        G.dist v0.1 x = i ∧ G.dist x w = p.length - i := by
    obtain ⟨i, hix, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hx
    refine ⟨i, hi, hix, ?_, ?_⟩
    · rw [← hix]
      exact geodesic_dist_getVert p hplen hi
    · calc
        G.dist x w = G.dist (p.getVert i) (p.getVert p.length) := by
          simp [hix]
        _ = p.length - i :=
          geodesic_dist_getVert_getVert p hplen hi (le_refl p.length)
  have hq_position (x : α) (hx : x ∈ q.support) :
      ∃ j : ℕ, j ≤ q.length ∧ q.getVert j = x ∧
        G.dist v0.1 x = j := by
    obtain ⟨j, hjx, hj⟩ := Walk.mem_support_iff_exists_getVert.mp hx
    exact ⟨j, hj, hjx, hjx ▸ geodesic_dist_getVert q hqlen hj⟩
  have hv2v1 : G.dist v2 v1 = 1 := by
    rw [dist_comm]
    simpa [v1, v2] using
      geodesic_dist_getVert_getVert q hqlen
        (show 1 ≤ 2 by omega) h2le
  have hno_cross {j : ℕ} (hj2 : 2 ≤ j) (hjr : j ≤ q.length)
      {x : α} (hxp : x ∈ p.support) :
      ¬G.Adj (q.getVert j) x := by
    intro hadj
    obtain ⟨i, hi, hix, hdi, htail⟩ := hp_position x hxp
    have hdq : G.dist v0.1 (q.getVert j) = j :=
      geodesic_dist_getVert q hqlen hjr
    have hv2q : G.dist v2 (q.getVert j) = j - 2 :=
      geodesic_dist_getVert_getVert q hqlen hj2 hjr
    have hxu : G.dist x (q.getVert j) = 1 :=
      dist_eq_one_iff_adj.mpr hadj.symm
    have hux : G.dist (q.getVert j) x = 1 :=
      dist_eq_one_iff_adj.mpr hadj
    have hleft := hG.dist_triangle
      (u := v0.1) (v := x) (w := q.getVert j)
    have hright₁ := hG.dist_triangle
      (u := v2) (v := q.getVert j) (w := x)
    have hright₂ := hG.dist_triangle
      (u := v2) (v := x) (w := w)
    rw [hdq, hdi, hxu] at hleft
    rw [hv2q, hux] at hright₁
    rw [htail] at hright₂
    rw [hrG] at hwfar
    omega
  have hq_not_mem_p {j : ℕ} (hj1 : 1 ≤ j) (hjr : j ≤ q.length) :
      q.getVert j ∉ p.support := by
    intro hmem
    obtain ⟨i, hi, hix, hdi, htail⟩ :=
      hp_position (q.getVert j) hmem
    have hdq : G.dist v0.1 (q.getVert j) = j :=
      geodesic_dist_getVert q hqlen hjr
    have hij : i = j := by omega
    have htri := hG.dist_triangle
      (u := v2) (v := q.getVert j) (w := w)
    by_cases hj : j = 1
    ·
      have hv2q1 : G.dist v2 (q.getVert 1) = 1 := by
        simpa [v1] using hv2v1
      rw [hj] at htail hij htri
      rw [hv2q1, htail, hij] at htri
      rw [hrG] at hwfar
      omega
    · have hj2 : 2 ≤ j := by omega
      have hv2q : G.dist v2 (q.getVert j) = j - 2 :=
        geodesic_dist_getVert_getVert q hqlen hj2 hjr
      rw [hv2q, htail, hij] at htri
      rw [hrG] at hwfar
      omega
  have hv1_cross_position {x : α} (hxp : x ∈ p.support)
      (hadj : G.Adj v1 x) :
      ∃ i : ℕ, i ≤ p.length ∧ i ≤ 1 ∧ p.getVert i = x := by
    obtain ⟨i, hi, hix, hdi, htail⟩ := hp_position x hxp
    refine ⟨i, hi, ?_, hix⟩
    by_contra hn
    have hi2 : 2 ≤ i := by omega
    have hv2x : G.dist v2 x ≤ 2 := by
      have htri := hG.dist_triangle (u := v2) (v := v1) (w := x)
      have hv1x : G.dist v1 x = 1 :=
        dist_eq_one_iff_adj.mpr hadj
      omega
    have htri := hG.dist_triangle (u := v2) (v := x) (w := w)
    rw [htail] at htri
    rw [hrG] at hwfar
    omega
  let left : Finset α := q.support.toFinset
  let right : Finset α := p.support.toFinset.erase v0.1
  let full : Finset α := left ∪ right
  have hdisj : Disjoint left right := by
    rw [Finset.disjoint_left]
    intro x hxleft hxright
    have hxq : x ∈ q.support := by simpa [left] using hxleft
    have hxp : x ∈ p.support := by
      exact List.mem_toFinset.mp (Finset.mem_of_mem_erase hxright)
    have hxne : x ≠ v0.1 := by
      simpa [right] using (Finset.ne_of_mem_erase hxright)
    obtain ⟨j, hj, hjx, hdj⟩ := hq_position x hxq
    have hjpos : 1 ≤ j := by
      by_contra hn
      have hj0 : j = 0 := by omega
      have hxv0 : x = v0.1 := by
        rw [← hjx, hj0]
        simp
      exact hxne hxv0
    exact hq_not_mem_p hjpos hj (hjx ▸ hxp)
  have hleftcard : left.card = r + 1 := by
    change q.support.toFinset.card = r + 1
    rw [List.toFinset_card_of_nodup hqpath.support_nodup,
      Walk.length_support, hqlenr]
  have hv0mem : v0.1 ∈ p.support.toFinset := by simp
  have hrightcard : right.card = p.length := by
    change (p.support.toFinset.erase v0.1).card = p.length
    rw [Finset.card_erase_of_mem hv0mem,
      List.toFinset_card_of_nodup hppath.support_nodup,
      Walk.length_support]
    omega
  have hfullcard : full.card = r + 1 + p.length := by
    change (left ∪ right).card = r + 1 + p.length
    rw [Finset.card_union_of_disjoint hdisj, hleftcard, hrightcard]
  let colorFull (x : α) : Fin 2 :=
    if x ∈ p.support then
      ⟨(r + G.dist v0.1 x) % 2, Nat.mod_lt _ (by omega)⟩
    else
      ⟨G.dist vr x % 2, Nat.mod_lt _ (by omega)⟩
  have hvRv1 : G.dist vr v1 = r - 1 := by
    rw [dist_comm]
    calc
      G.dist v1 vr =
          G.dist (q.getVert 1) (q.getVert q.length) := by simp [v1]
      _ = q.length - 1 :=
        geodesic_dist_getVert_getVert q hqlen h1le (le_refl q.length)
      _ = r - 1 := by rw [hqlenr]
  have hqrevlen : q.reverse.length = G.dist vr v0.1 := by
    rw [Walk.length_reverse, dist_comm, ← hqlen, hqlenr]
  have hcolor_full
      (hchord : p.length = 0 ∨ ¬G.Adj v1 (p.getVert 1))
      {x y : α} (hxfull : x ∈ full) (hyfull : y ∈ full)
      (hxy : G.Adj x y) :
      colorFull x ≠ colorFull y := by
    have hcross {a b : α}
        (hap : a ∈ p.support) (hbp : b ∉ p.support)
        (hafull : a ∈ full) (hbfull : b ∈ full)
        (hab : G.Adj a b) :
        (colorFull a).val ≠ (colorFull b).val := by
      have hbq : b ∈ q.support := by
        rcases Finset.mem_union.mp hbfull with hbl | hbr
        · simpa [left] using hbl
        · have : b ∈ p.support := by
            exact List.mem_toFinset.mp
              (Finset.mem_of_mem_erase (by simpa [right] using hbr))
          exact (hbp this).elim
      obtain ⟨j, hj, hjb, -⟩ := hq_position b hbq
      have hjpos : 1 ≤ j := by
        by_contra hn
        have hj0 : j = 0 := by omega
        have hbv0 : b = v0.1 := by
          rw [← hjb, hj0]
          simp
        apply hbp
        rw [hbv0]
        exact p.start_mem_support
      have hjone : j = 1 := by
        by_contra hn
        have hj2 : 2 ≤ j := by omega
        exact hno_cross hj2 hj hap (hjb ▸ hab.symm)
      have hbv1 : b = v1 := by
        rw [hjone] at hjb
        simpa [v1] using hjb.symm
      have hav0 : a = v0.1 := by
        have hva : G.Adj v1 a := by simpa [hbv1] using hab.symm
        obtain ⟨i, hip, hi, hia⟩ := hv1_cross_position hap hva
        have hi_cases : i = 0 ∨ i = 1 := by omega
        rcases hi_cases with rfl | rfl
        · simpa using hia.symm
        · rcases hchord with hpzero | hnochord
          · omega
          · exact (hnochord (by simpa [v1, hia] using hva)).elim
      simp only [colorFull, hap, if_pos, hbp]
      rw [hav0, hbv1, dist_self, hvRv1]
      change (r % 2) ≠ ((r - 1) % 2)
      omega
    apply Fin.ne_of_val_ne
    by_cases hxp : x ∈ p.support
    · by_cases hyp : y ∈ p.support
      · simp only [colorFull, hxp, if_pos, hyp]
        have hpar :=
          geodesic_adjacent_support_parity p hplen hxp hyp hxy
        omega
      · exact hcross hxp hyp hxfull hyfull hxy
    · by_cases hyp : y ∈ p.support
      · exact (hcross hyp hxp hyfull hxfull hxy.symm).symm
      · have hxq : x ∈ q.support := by
          rcases Finset.mem_union.mp hxfull with hxl | hxr
          · simpa [left] using hxl
          · have : x ∈ p.support := by
              exact List.mem_toFinset.mp
                (Finset.mem_of_mem_erase (by simpa [right] using hxr))
            exact (hxp this).elim
        have hyq : y ∈ q.support := by
          rcases Finset.mem_union.mp hyfull with hyl | hyr
          · simpa [left] using hyl
          · have : y ∈ p.support := by
              exact List.mem_toFinset.mp
                (Finset.mem_of_mem_erase (by simpa [right] using hyr))
            exact (hyp this).elim
        simp only [colorFull, hxp, hyp]
        have hpar := geodesic_adjacent_support_parity
          q.reverse hqrevlen (by simpa using hxq) (by simpa using hyq) hxy
        exact hpar
  have hbip_full
      (hchord : p.length = 0 ∨ ¬G.Adj v1 (p.getVert 1)) :
      (G.induce (full : Set α)).IsBipartite := by
    refine ⟨SimpleGraph.Coloring.mk (fun x ↦ colorFull x.1) ?_⟩
    intro x y hxy
    exact hcolor_full hchord x.2 y.2 hxy
  have hv1v0 : G.dist v1 v0.1 = 1 := by
    rw [dist_comm]
    simpa [v1] using
      geodesic_dist_getVert_getVert q hqlen
        (show 0 ≤ 1 by omega) h1le
  have hsafe_short (hpshort : p.length = r - 2) :
      p.length = 0 ∨ ¬G.Adj v1 (p.getVert 1) := by
    by_cases hpzero : p.length = 0
    · exact Or.inl hpzero
    · right
      intro hadj
      have hpone : 1 ≤ p.length := Nat.one_le_iff_ne_zero.mpr hpzero
      have hv1p1 : G.dist v1 (p.getVert 1) = 1 :=
        dist_eq_one_iff_adj.mpr hadj
      have hp1w : G.dist (p.getVert 1) w = p.length - 1 := by
        calc
          G.dist (p.getVert 1) w =
              G.dist (p.getVert 1) (p.getVert p.length) := by simp
          _ = p.length - 1 :=
            geodesic_dist_getVert_getVert p hplen hpone (le_refl p.length)
      have htri₁ := hG.dist_triangle (u := v2) (v := v1) (w := w)
      have htri₂ :=
        hG.dist_triangle (u := v1) (v := p.getVert 1) (w := w)
      rw [hv2v1] at htri₁
      rw [hv1p1, hp1w] at htri₂
      rw [hrG] at hwfar
      omega
  rcases hp_cases with hpshort | hplong
  ·
    have hsafe := hsafe_short hpshort
    have hnear_full (x : α) (hx : x ∈ full) :
        G.dist v1 x ≤ r - 1 := by
      rcases Finset.mem_union.mp hx with hxq | hxp
      ·
        have hxqs : x ∈ q.support := by simpa [left] using hxq
        obtain ⟨j, hj, hjx, -⟩ := hq_position x hxqs
        by_cases hj0 : j = 0
        · have hxv0 : x = v0.1 := by
            rw [← hjx, hj0]
            simp
          rw [hxv0, hv1v0]
          omega
        · have hj1 : 1 ≤ j := by omega
          have hd :
              G.dist v1 x = j - 1 := by
            rw [← hjx]
            simpa [v1] using
              geodesic_dist_getVert_getVert q hqlen hj1 hj
          rw [hd]
          omega
      ·
        have hxps : x ∈ p.support := by
          exact List.mem_toFinset.mp
            (Finset.mem_of_mem_erase (by simpa [right] using hxp))
        obtain ⟨i, hi, -, hdi, -⟩ := hp_position x hxps
        have htri := hG.dist_triangle (u := v1) (v := v0.1) (w := x)
        rw [hv1v0, hdi] at htri
        omega
    have hnear_one_full (x : α) (hx : x ∈ full)
        (hcx : colorFull x = (1 : Fin 2)) :
        G.dist v1 x ≤ r - 2 := by
      rcases Finset.mem_union.mp hx with hxq | hxp
      ·
        have hxqs : x ∈ q.support := by simpa [left] using hxq
        obtain ⟨j, hj, hjx, -⟩ := hq_position x hxqs
        by_cases hj0 : j = 0
        · have hxv0 : x = v0.1 := by
            rw [← hjx, hj0]
            simp
          have hxps : x ∈ p.support := by
            rw [hxv0]
            exact p.start_mem_support
          have hcval := congrArg Fin.val hcx
          simp only [colorFull, hxps, if_pos] at hcval
          rw [hxv0, dist_self] at hcval
          change r % 2 = 1 at hcval
          rw [hxv0, hv1v0]
          omega
        ·
          have hj1 : 1 ≤ j := by omega
          have hxpn : x ∉ p.support := by
            intro hxps
            exact hq_not_mem_p hj1 hj (hjx ▸ hxps)
          have hdvrx : G.dist vr x = r - j := by
            rw [dist_comm, ← hjx]
            calc
              G.dist (q.getVert j) vr =
                  G.dist (q.getVert j) (q.getVert q.length) := by simp
              _ = q.length - j :=
                geodesic_dist_getVert_getVert q hqlen hj (le_refl q.length)
              _ = r - j := by rw [hqlenr]
          have hdv1x : G.dist v1 x = j - 1 := by
            rw [← hjx]
            simpa [v1] using
              geodesic_dist_getVert_getVert q hqlen hj1 hj
          have hcval := congrArg Fin.val hcx
          simp only [colorFull, hxpn] at hcval
          change G.dist vr x % 2 = 1 at hcval
          rw [hdvrx] at hcval
          rw [hdv1x]
          omega
      ·
        have hxps : x ∈ p.support := by
          exact List.mem_toFinset.mp
            (Finset.mem_of_mem_erase (by simpa [right] using hxp))
        obtain ⟨i, hi, -, hdi, -⟩ := hp_position x hxps
        have hcval := congrArg Fin.val hcx
        simp only [colorFull, hxps, if_pos] at hcval
        rw [hdi] at hcval
        change (r + i) % 2 = 1 at hcval
        have htri := hG.dist_triangle (u := v1) (v := v0.1) (w := x)
        rw [hv1v0, hdi] at htri
        omega
    by_contra hn
    have hsmall :
        largestInducedBipartiteSubgraphSize G < 2 * r :=
      Nat.lt_of_not_ge hn
    have hradsmall :=
      almost_bipartite_core_forces_small_radius
        G hG r hr full v1 colorFull
        (by
          intro x y hx hy hxy
          exact hcolor_full hsafe hx hy hxy)
        (by rw [hfullcard, hpshort]; omega)
        hnear_full hnear_one_full hsmall
    rw [hrG] at hradsmall
    omega
  ·
    by_cases hchord : G.Adj v1 (p.getVert 1)
    ·
      let drop : Finset α := left.erase v0.1 ∪ right
      have hv0left : v0.1 ∈ left := by
        change v0.1 ∈ q.support.toFinset
        simp
      have hdropdisj : Disjoint (left.erase v0.1) right :=
        hdisj.mono (Finset.erase_subset _ _) (by rfl)
      have hdropcard : drop.card = 2 * r - 1 := by
        change (left.erase v0.1 ∪ right).card = 2 * r - 1
        rw [Finset.card_union_of_disjoint hdropdisj,
          Finset.card_erase_of_mem hv0left, hleftcard, hrightcard, hplong]
        omega
      have hdrop_ne_v0 {x : α} (hx : x ∈ drop) : x ≠ v0.1 := by
        rcases Finset.mem_union.mp hx with hxl | hxr
        · exact Finset.ne_of_mem_erase hxl
        · simpa [right] using (Finset.ne_of_mem_erase hxr)
      let colorDrop (x : α) : Fin 2 :=
        if x ∈ p.support then
          ⟨(r - 1 + G.dist v0.1 x) % 2, Nat.mod_lt _ (by omega)⟩
        else
          ⟨G.dist vr x % 2, Nat.mod_lt _ (by omega)⟩
      have hpone : 1 ≤ p.length := by omega
      have hpdist1 : G.dist v0.1 (p.getVert 1) = 1 :=
        geodesic_dist_getVert p hplen hpone
      have hcolor_drop {x y : α}
          (hxdrop : x ∈ drop) (hydrop : y ∈ drop)
          (hxy : G.Adj x y) :
          colorDrop x ≠ colorDrop y := by
        have hcross {a b : α}
            (hap : a ∈ p.support) (hbp : b ∉ p.support)
            (hadrop : a ∈ drop) (hbdrop : b ∈ drop)
            (hab : G.Adj a b) :
            (colorDrop a).val ≠ (colorDrop b).val := by
          have hbq : b ∈ q.support := by
            rcases Finset.mem_union.mp hbdrop with hbl | hbr
            · have hblleft : b ∈ left := Finset.mem_of_mem_erase hbl
              simpa [left] using hblleft
            · have : b ∈ p.support := by
                exact List.mem_toFinset.mp
                  (Finset.mem_of_mem_erase (by simpa [right] using hbr))
              exact (hbp this).elim
          obtain ⟨j, hj, hjb, -⟩ := hq_position b hbq
          have hjpos : 1 ≤ j := by
            by_contra hn
            have hj0 : j = 0 := by omega
            have hbv0 : b = v0.1 := by
              rw [← hjb, hj0]
              simp
            apply hbp
            rw [hbv0]
            exact p.start_mem_support
          have hjone : j = 1 := by
            by_contra hn
            have hj2 : 2 ≤ j := by omega
            exact hno_cross hj2 hj hap (hjb ▸ hab.symm)
          have hbv1 : b = v1 := by
            rw [hjone] at hjb
            simpa [v1] using hjb.symm
          have hap1 : a = p.getVert 1 := by
            have hva : G.Adj v1 a := by simpa [hbv1] using hab.symm
            obtain ⟨i, hip, hi, hia⟩ := hv1_cross_position hap hva
            have hi_cases : i = 0 ∨ i = 1 := by omega
            rcases hi_cases with rfl | rfl
            · have hav0 : a = v0.1 := by simpa using hia.symm
              exact ((hdrop_ne_v0 hadrop) hav0).elim
            · exact hia.symm
          simp only [colorDrop, hap, if_pos, hbp]
          rw [hap1, hbv1, hpdist1, hvRv1]
          change ((r - 1 + 1) % 2) ≠ ((r - 1) % 2)
          omega
        apply Fin.ne_of_val_ne
        by_cases hxp : x ∈ p.support
        · by_cases hyp : y ∈ p.support
          · simp only [colorDrop, hxp, if_pos, hyp]
            have hpar :=
              geodesic_adjacent_support_parity p hplen hxp hyp hxy
            omega
          · exact hcross hxp hyp hxdrop hydrop hxy
        · by_cases hyp : y ∈ p.support
          · exact (hcross hyp hxp hydrop hxdrop hxy.symm).symm
          ·
            have hxq : x ∈ q.support := by
              rcases Finset.mem_union.mp hxdrop with hxl | hxr
              · have hxlleft : x ∈ left := Finset.mem_of_mem_erase hxl
                simpa [left] using hxlleft
              · have : x ∈ p.support := by
                  exact List.mem_toFinset.mp
                    (Finset.mem_of_mem_erase (by simpa [right] using hxr))
                exact (hxp this).elim
            have hyq : y ∈ q.support := by
              rcases Finset.mem_union.mp hydrop with hyl | hyr
              · have hylleft : y ∈ left := Finset.mem_of_mem_erase hyl
                simpa [left] using hylleft
              · have : y ∈ p.support := by
                  exact List.mem_toFinset.mp
                    (Finset.mem_of_mem_erase (by simpa [right] using hyr))
                exact (hyp this).elim
            simp only [colorDrop, hxp, hyp]
            exact geodesic_adjacent_support_parity
              q.reverse hqrevlen
              (by simpa using hxq) (by simpa using hyq) hxy
      have hnear_drop (x : α) (hx : x ∈ drop) :
          G.dist v1 x ≤ r - 1 := by
        rcases Finset.mem_union.mp hx with hxq | hxp
        ·
          have hxqs : x ∈ q.support := by
            have hxqleft : x ∈ left := Finset.mem_of_mem_erase hxq
            simpa [left] using hxqleft
          obtain ⟨j, hj, hjx, -⟩ := hq_position x hxqs
          have hj1 : 1 ≤ j := by
            by_contra hn
            have hj0 : j = 0 := by omega
            have hxv0 : x = v0.1 := by
              rw [← hjx, hj0]
              simp
            exact hdrop_ne_v0 hx hxv0
          have hd : G.dist v1 x = j - 1 := by
            rw [← hjx]
            simpa [v1] using
              geodesic_dist_getVert_getVert q hqlen hj1 hj
          rw [hd]
          omega
        ·
          have hxps : x ∈ p.support := by
            exact List.mem_toFinset.mp
              (Finset.mem_of_mem_erase (by simpa [right] using hxp))
          obtain ⟨i, hi, hix, -, -⟩ := hp_position x hxps
          have hi1 : 1 ≤ i := by
            by_contra hn
            have hi0 : i = 0 := by omega
            have hxv0 : x = v0.1 := by
              rw [← hix, hi0]
              simp
            exact hdrop_ne_v0 hx hxv0
          have hp1x : G.dist (p.getVert 1) x = i - 1 := by
            rw [← hix]
            exact geodesic_dist_getVert_getVert p hplen hi1 hi
          have htri :=
            hG.dist_triangle (u := v1) (v := p.getVert 1) (w := x)
          rw [dist_eq_one_iff_adj.mpr hchord, hp1x] at htri
          omega
      have hnear_one_drop (x : α) (hx : x ∈ drop)
          (hcx : colorDrop x = (1 : Fin 2)) :
          G.dist v1 x ≤ r - 2 := by
        rcases Finset.mem_union.mp hx with hxq | hxp
        ·
          have hxqs : x ∈ q.support := by
            have hxqleft : x ∈ left := Finset.mem_of_mem_erase hxq
            simpa [left] using hxqleft
          obtain ⟨j, hj, hjx, -⟩ := hq_position x hxqs
          have hj1 : 1 ≤ j := by
            by_contra hn
            have hj0 : j = 0 := by omega
            have hxv0 : x = v0.1 := by
              rw [← hjx, hj0]
              simp
            exact hdrop_ne_v0 hx hxv0
          have hxpn : x ∉ p.support := by
            intro hxps
            exact hq_not_mem_p hj1 hj (hjx ▸ hxps)
          have hdvrx : G.dist vr x = r - j := by
            rw [dist_comm, ← hjx]
            calc
              G.dist (q.getVert j) vr =
                  G.dist (q.getVert j) (q.getVert q.length) := by simp
              _ = q.length - j :=
                geodesic_dist_getVert_getVert q hqlen hj (le_refl q.length)
              _ = r - j := by rw [hqlenr]
          have hdv1x : G.dist v1 x = j - 1 := by
            rw [← hjx]
            simpa [v1] using
              geodesic_dist_getVert_getVert q hqlen hj1 hj
          have hcval := congrArg Fin.val hcx
          simp only [colorDrop, hxpn] at hcval
          change G.dist vr x % 2 = 1 at hcval
          rw [hdvrx] at hcval
          rw [hdv1x]
          omega
        ·
          have hxps : x ∈ p.support := by
            exact List.mem_toFinset.mp
              (Finset.mem_of_mem_erase (by simpa [right] using hxp))
          obtain ⟨i, hi, hix, hdi, -⟩ := hp_position x hxps
          have hi1 : 1 ≤ i := by
            by_contra hn
            have hi0 : i = 0 := by omega
            have hxv0 : x = v0.1 := by
              rw [← hix, hi0]
              simp
            exact hdrop_ne_v0 hx hxv0
          have hp1x : G.dist (p.getVert 1) x = i - 1 := by
            rw [← hix]
            exact geodesic_dist_getVert_getVert p hplen hi1 hi
          have hcval := congrArg Fin.val hcx
          simp only [colorDrop, hxps, if_pos] at hcval
          rw [hdi] at hcval
          change (r - 1 + i) % 2 = 1 at hcval
          have htri :=
            hG.dist_triangle (u := v1) (v := p.getVert 1) (w := x)
          rw [dist_eq_one_iff_adj.mpr hchord, hp1x] at htri
          omega
      by_contra hn
      have hsmall :
          largestInducedBipartiteSubgraphSize G < 2 * r :=
        Nat.lt_of_not_ge hn
      have hradsmall :=
        almost_bipartite_core_forces_small_radius
          G hG r hr drop v1 colorDrop
          (by
            intro x y hx hy hxy
            exact hcolor_drop hx hy hxy)
          hdropcard hnear_drop hnear_one_drop hsmall
      rw [hrG] at hradsmall
      omega
    ·
      have hle :=
        card_le_largestInducedBipartiteSubgraphSize'
          (hbip_full (Or.inr hchord))
      rw [hfullcard, hplong] at hle
      omega

private lemma largestInducedBipartiteSubgraphSize_induce_compl_singleton_le
    (G : SimpleGraph α) (v : α) :
    largestInducedBipartiteSubgraphSize
        (G.induce ({v}ᶜ : Set α)) ≤
      largestInducedBipartiteSubgraphSize G := by
  classical
  unfold largestInducedBipartiteSubgraphSize
  apply csSup_le
  · refine ⟨0, ∅, ?_, rfl⟩
    refine ⟨SimpleGraph.Coloring.mk (fun _ ↦ 0) ?_⟩
    intro x y hxy
    have hxfalse :
        x.1 ∉ (↑(∅ : Finset ({v}ᶜ : Set α)) : Set ({v}ᶜ : Set α)) := by
      simp
    exact (hxfalse x.2).elim
  · rintro n ⟨t, ht, rfl⟩
    obtain ⟨u, hu, hcard⟩ :=
      lift_bipartite_from_vertex_deletion G v ht
    rw [← hcard]
    exact card_le_largestInducedBipartiteSubgraphSize' hu

omit [DecidableEq α] in
private theorem radius_bipartite_bound_aux
    (G : SimpleGraph α) (hG : G.Connected) :
    2 * G.radius.toNat ≤ largestInducedBipartiteSubgraphSize G := by
  classical
  let P : ∀ (β : Type u) [Fintype β], Prop :=
    fun β _ ↦ ∀ K : SimpleGraph β, K.Connected →
      2 * K.radius.toNat ≤ largestInducedBipartiteSubgraphSize K
  refine Fintype.induction_subsingleton_or_nontrivial
    (P := P) α ?_ ?_ G hG
  · intro β inst hsub K hK
    have hr0 : K.radius = 0 :=
      K.radius_eq_zero_iff.mpr ⟨hK.nonempty, hsub⟩
    simp [hr0]
  · intro β inst hnontriv ih K hK
    by_cases hrsmall : K.radius.toNat ≤ 1
    · obtain ⟨t, ht, hcard⟩ := radius_one_bound K hK hrsmall
      exact hcard.trans (card_le_largestInducedBipartiteSubgraphSize' ht)
    ·
      have hr : 2 ≤ K.radius.toNat := by omega
      obtain ⟨v, hdel⟩ :=
        hK.exists_connected_induce_compl_singleton_of_finite_nontrivial
      let H := K.induce ({v}ᶜ : Set β)
      have hcardlt :
          Fintype.card ({v}ᶜ : Set β) < Fintype.card β :=
        Fintype.card_subtype_lt (x := v) (by simp)
      have hHbound :
          2 * H.radius.toNat ≤ largestInducedBipartiteSubgraphSize H :=
        (ih ({v}ᶜ : Set β) hcardlt) H hdel
      by_cases hrad :
          K.radius.toNat ≤ H.radius.toNat
      ·
        calc
          2 * K.radius.toNat ≤ 2 * H.radius.toNat :=
            Nat.mul_le_mul_left 2 hrad
          _ ≤ largestInducedBipartiteSubgraphSize H := hHbound
          _ ≤ largestInducedBipartiteSubgraphSize K := by
            exact
              largestInducedBipartiteSubgraphSize_induce_compl_singleton_le K v
      ·
        apply critical_case_radius_bipartite
          K hK K.radius.toNat hr rfl v hdel
        exact Nat.lt_of_not_ge hrad

/-
Every finite connected nontrivial graph has an induced bipartite subgraph
on at least twice its radius many vertices.
-/
omit [DecidableEq α] in
theorem two_mul_radius_le_largestInducedBipartiteSubgraphSize
    (G : SimpleGraph α) [Nontrivial α] (hG : G.Connected) :
    2 * G.radius.toNat ≤ largestInducedBipartiteSubgraphSize G :=
  radius_bipartite_bound_aux G hG

end WrittenOnTheWallII.GraphConjecture198a
