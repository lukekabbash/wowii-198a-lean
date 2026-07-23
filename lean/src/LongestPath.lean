/- Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0 . -/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Walks.Subwalks

/-!
# A longest-path lemma for graphs with independence number at most three

This file isolates the elementary graph-theoretic part needed in the diameter-two
case of Written on the Wall II, Conjecture 198a.  The eventual theorem is:

> A finite connected graph in which deleting any one vertex leaves a connected
> graph, and which has no independent set of four vertices, has a Hamiltonian path.

The proof uses only a longest path and two explicit path reroutings.  In
particular, it avoids importing a formal version of the Chvátal--Erdős theorem.
-/

open Finset Function

namespace SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- Pointwise form of "there is no independent set on four vertices".

The pointwise formulation is convenient in longest-path arguments and avoids
repeated `Finset` bookkeeping. -/
def NoIndependentFour (G : SimpleGraph V) : Prop :=
  ∀ ⦃a b c d : V⦄,
    a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    G.Adj a b ∨ G.Adj a c ∨ G.Adj a d ∨
      G.Adj b c ∨ G.Adj b d ∨ G.Adj c d

/-- Every one-vertex deletion is connected.  This is the exact connectivity
hypothesis used by the elementary proof below. -/
def VertexDeletionConnected (G : SimpleGraph V) : Prop :=
  ∀ c : V, (G.induce ({c}ᶜ : Set V)).Connected

/-- `IndepSetFree 4` implies the pointwise four-vertex condition. -/
lemma noIndependentFour_of_indepSetFree [DecidableEq V]
    (h : G.IndepSetFree 4) : G.NoIndependentFour := by
  intro a b c d hab hac had hbc hbd hcd
  by_contra hn
  push_neg at hn
  apply h {a, b, c, d}
  refine ⟨?_, by simp [hab, hac, had, hbc, hbd, hcd]⟩
  rw [G.isIndepSet_iff]
  intro x hx y hy hxy
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with (rfl | rfl | rfl | rfl) <;>
    rcases hy with (rfl | rfl | rfl | rfl) <;>
    simp_all [G.adj_comm]

/-- In a connected graph, every nontrivial vertex cut has a crossing edge. -/
lemma Connected.exists_adj_across
    (hG : G.Connected) {s : Set V} {x y : V} (hx : x ∉ s) (hy : y ∈ s) :
    ∃ a b, a ∉ s ∧ b ∈ s ∧ G.Adj a b := by
  obtain ⟨p⟩ := hG x y
  let rec go {a b : V} (p : G.Walk a b) (ha : a ∉ s) (hb : b ∈ s) :
      ∃ z w, z ∉ s ∧ w ∈ s ∧ G.Adj z w := by
    match p with
    | .nil => exact (ha hb).elim
    | .cons (v := z) haz q =>
        by_cases hz : z ∈ s
        · exact ⟨a, z, ha, hz, haz⟩
        · exact go q hz hb
  exact go p hx hy

namespace Walk

variable {u v : V} {p : G.Walk u v}

/-- A vertex of `p` incident with an edge from outside `p`. -/
def IsAttachment (p : G.Walk u v) (z : V) : Prop :=
  z ∈ p.support ∧ ∃ x, x ∉ p.support ∧ G.Adj x z

/-- The contiguous part of a walk between positions `i` and `j`. -/
def segment (p : G.Walk u v) (i j : ℕ) (hij : i ≤ j) :
    G.Walk (p.getVert i) (p.getVert j) :=
  ((p.drop i).take (j - i)).copy (by simp) (by simp; congr 1; omega)

@[simp]
lemma segment_length (p : G.Walk u v) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ p.length) :
    (p.segment i j hij).length = j - i := by
  simp only [segment, length_copy, take_length, drop_length]
  rw [Nat.min_eq_left (by omega)]

lemma IsPath.segment (hp : p.IsPath) {i j : ℕ} (hij : i ≤ j) :
    (p.segment i j hij).IsPath := by
  rw [Walk.segment, isPath_copy]
  exact isPath_of_isSubwalk
    ((isSubwalk_take (p.drop i) (j - i)).trans (isSubwalk_drop p i)) hp

lemma segment_support_subset (p : G.Walk u v) {i j : ℕ} (hij : i ≤ j) :
    (p.segment i j hij).support ⊆ p.support := by
  intro z hz
  rw [segment, support_copy] at hz
  exact ((isSubwalk_take (p.drop i) (j - i)).trans
    (isSubwalk_drop p i)).support_subset hz

lemma mem_segment_support_iff (_hp : p.IsPath) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ p.length) {z : V} :
    z ∈ (p.segment i j hij).support ↔
      ∃ k, i ≤ k ∧ k ≤ j ∧ p.getVert k = z := by
  constructor
  · intro hz
    obtain ⟨n, hn, hnl⟩ := mem_support_iff_exists_getVert.mp hz
    have hnl' : n ≤ j - i := by
      rw [segment_length _ hij hj] at hnl
      exact hnl
    refine ⟨i + n, by omega, ?_, ?_⟩
    · omega
    · simp [segment] at hn
      rw [Nat.min_eq_right hnl'] at hn
      exact hn
  · rintro ⟨k, hik, hkj, rfl⟩
    apply mem_support_iff_exists_getVert.mpr
    refine ⟨k - i, ?_, ?_⟩
    · simp [segment]
      rw [Nat.min_eq_right (by omega), Nat.add_sub_of_le hik]
    · rw [segment_length _ hij hj]
      omega

/-- The initial endpoint of a longest path has no neighbor outside the path. -/
lemma IsPath.not_adj_start_of_forall_length_le
    (hp : p.IsPath)
    (hmax : ∀ (a b : V) (q : G.Walk a b), q.IsPath → q.length ≤ p.length)
    {x : V} (hx : x ∉ p.support) : ¬G.Adj x u := by
  intro hxu
  have hxp : (p.cons hxu).IsPath := hp.cons hx
  have := hmax x v (p.cons hxu) hxp
  simp only [length_cons] at this
  omega

/-- The final endpoint of a longest path has no neighbor outside the path. -/
lemma IsPath.not_adj_end_of_forall_length_le
    (hp : p.IsPath)
    (hmax : ∀ (a b : V) (q : G.Walk a b), q.IsPath → q.length ≤ p.length)
    {x : V} (hx : x ∉ p.support) : ¬G.Adj v x := by
  intro hvx
  have hxp : (p.concat hvx).IsPath := hp.concat hx hvx
  have := hmax u x (p.concat hvx) hxp
  simp only [length_concat] at this
  omega

/-- A path obtained by appending two paths is a path when their only common
vertex is the gluing endpoint. -/
lemma IsPath.append_of_forall_mem
    {w : V} {q : G.Walk v w} (hp : p.IsPath) (hq : q.IsPath)
    (hinter : ∀ z, z ∈ p.support → z ∈ q.support → z = v) :
    (p.append q).IsPath := by
  rw [isPath_def, support_append, List.nodup_append']
  refine ⟨hp.support_nodup, hq.support_nodup.tail, ?_⟩
  rw [List.disjoint_iff_ne]
  intro a ha b hb hab
  have hbq : b ∈ q.support := List.mem_of_mem_tail hb
  have hav : a = v := hinter a ha (hab ▸ hbq)
  have hbv : b ≠ v := by
    intro hbv
    have hb' : v ∈ q.support.tail := hbv ▸ hb
    have hnod := hq.support_nodup
    rw [q.support_eq_cons, List.nodup_cons] at hnod
    exact hnod.1 hb'
  exact hbv (hab ▸ hav)

/-- If a connected graph has a nonspanning longest path, the endpoints of
that path are nonadjacent.

Indeed, an endpoint edge closes the path into a cycle.  A crossing edge from
outside the path can then be attached after rotating the cycle, producing a
strictly longer path. -/
lemma IsPath.not_adj_endpoints_of_connected_of_forall_length_le
    [DecidableEq V] (hp : p.IsPath) (hG : G.Connected)
    (hmax : ∀ (a b : V) (q : G.Walk a b), q.IsPath → q.length ≤ p.length)
    {x : V} (hx : x ∉ p.support) : ¬G.Adj u v := by
  obtain ⟨a, b, ha, hb, hab⟩ :=
    hG.exists_adj_across (s := {z | z ∈ p.support}) hx p.start_mem_support
  have hbu : b ≠ u := by
    rintro rfl
    exact hp.not_adj_start_of_forall_length_le hmax ha hab
  have hbv : b ≠ v := by
    rintro rfl
    exact hp.not_adj_end_of_forall_length_le hmax ha hab.symm
  obtain ⟨i, hbi, hi⟩ := mem_support_iff_exists_getVert.mp hb
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact hbu (by simpa using hbi.symm)
  have hiL : i ≠ p.length := by
    intro hiL
    exact hbv (by simpa [hiL] using hbi.symm)
  have hlen : 2 ≤ p.length := by omega
  intro huv
  have hedge : s(u, v) ∉ p.edges := by
    intro hedge
    have hv : v = p.snd := hp.eq_snd_of_mem_edges hedge
    have hget : p.getVert 1 = p.getVert p.length := by
      simpa [snd] using hv.symm
    have hone := hp.getVert_injOn
      (show 1 ∈ {i | i ≤ p.length} by simp only [Set.mem_setOf_eq]; omega)
      (show p.length ∈ {i | i ≤ p.length} by simp) hget
    omega
  let c : G.Walk u u := p.concat huv.symm
  have hc : c.IsCycle := by
    have hcrev : c.reverse.IsCycle := by
      change (p.concat huv.symm).reverse.IsCycle
      rw [reverse_concat]
      rw [cons_isCycle_iff]
      exact ⟨hp.reverse, by simpa using hedge⟩
    simpa using hcrev.reverse
  have hbc : b ∈ c.support := by
    have hb' : b ∈ p.support := hb
    simp [c, hb']
  let cr : G.Walk b b := c.rotate hbc
  have hcr : cr.IsCycle := hc.rotate hbc
  have hcr_not_nil : ¬cr.Nil := by
    intro hnil
    exact hcr.ne_nil hnil.eq_nil
  have htail : cr.tail.IsPath := by
    apply IsPath.mk'
    rw [support_tail_of_not_nil cr hcr_not_nil]
    exact hcr.support_nodup
  have hat : a ∉ cr.tail.support := by
    intro hat
    have hat' : a ∈ cr.support.tail := by
      rwa [← support_tail_of_not_nil cr hcr_not_nil]
    have hacr : a ∈ cr.support := List.mem_of_mem_tail hat'
    have hac : a ∈ c.support := (mem_support_rotate_iff c hbc).mp hacr
    have hac' : a ∈ p.support ∨ a = u := by
      simpa [c] using hac
    rcases hac' with hac | rfl
    · exact ha hac
    · exact ha p.start_mem_support
  have hlong : (cr.tail.concat hab.symm).IsPath :=
    htail.concat hat hab.symm
  have hlencr : cr.length = c.length := by
    rw [← length_darts, ← length_darts]
    obtain ⟨n, hn⟩ := rotate_darts c hbc
    simpa using congrArg List.length hn
  have hq : (cr.tail.concat hab.symm).length = p.length + 1 := by
    rw [length_concat]
    calc
      cr.tail.length + 1 = cr.length := length_tail_add_one hcr_not_nil
      _ = c.length := hlencr
      _ = p.length + 1 := by simp [c]
  have := hmax _ _ (cr.tail.concat hab.symm) hlong
  omega

/-- A nonspanning longest path in a connected graph has distinct endpoints. -/
lemma IsPath.start_ne_end_of_connected_of_forall_length_le
    [DecidableEq V] (hp : p.IsPath) (hG : G.Connected)
    (hmax : ∀ (a b : V) (q : G.Walk a b), q.IsPath → q.length ≤ p.length)
    {x : V} (hx : x ∉ p.support) : u ≠ v := by
  obtain ⟨a, b, ha, hb, hab⟩ :=
    hG.exists_adj_across (s := {z | z ∈ p.support}) hx p.start_mem_support
  have hbu : b ≠ u := by
    rintro rfl
    exact hp.not_adj_start_of_forall_length_le hmax ha hab
  intro huv
  subst v
  have hpnil : p = Walk.nil := (isPath_iff_eq_nil p).mp hp
  subst p
  exact hbu (by simpa using hb)

/-- Vertices outside a nonspanning longest path form a clique when the graph
has no independent set of four vertices. -/
lemma IsPath.adj_of_not_mem_support_of_not_mem_support
    [DecidableEq V] (hp : p.IsPath) (hG : G.Connected)
    (hfour : G.NoIndependentFour)
    (hmax : ∀ (a b : V) (q : G.Walk a b), q.IsPath → q.length ≤ p.length)
    {x y : V} (hx : x ∉ p.support) (hy : y ∉ p.support) (hxy : x ≠ y) :
    G.Adj x y := by
  have huv : u ≠ v :=
    hp.start_ne_end_of_connected_of_forall_length_le hG hmax hx
  have hux : u ≠ x := fun h ↦ hx (h ▸ p.start_mem_support)
  have huy : u ≠ y := fun h ↦ hy (h ▸ p.start_mem_support)
  have hvx : v ≠ x := fun h ↦ hx (h ▸ p.end_mem_support)
  have hvy : v ≠ y := fun h ↦ hy (h ▸ p.end_mem_support)
  have hnuv : ¬G.Adj u v :=
    hp.not_adj_endpoints_of_connected_of_forall_length_le hG hmax hx
  have hnux : ¬G.Adj u x := by
    rw [G.adj_comm]
    exact hp.not_adj_start_of_forall_length_le hmax hx
  have hnuy : ¬G.Adj u y := by
    rw [G.adj_comm]
    exact hp.not_adj_start_of_forall_length_le hmax hy
  have hnvx : ¬G.Adj v x :=
    hp.not_adj_end_of_forall_length_le hmax hx
  have hnvy : ¬G.Adj v y :=
    hp.not_adj_end_of_forall_length_le hmax hy
  rcases hfour huv hux huy hvx hvy hxy with
    huv' | hux' | huy' | hvx' | hvy' | hxy'
  · exact (hnuv huv').elim
  · exact (hnux hux').elim
  · exact (hnuy huy').elim
  · exact (hnvx hvx').elim
  · exact (hnvy hvy').elim
  · exact hxy'

/-- One-vertex deletion connectivity supplies two distinct attachment
vertices on any nonspanning longest path. -/
lemma IsPath.exists_two_attachments
    [DecidableEq V] (hp : p.IsPath) (hG : G.Connected)
    (hdelete : G.VertexDeletionConnected)
    (hmax : ∀ (a b : V) (q : G.Walk a b), q.IsPath → q.length ≤ p.length)
    {x : V} (hx : x ∉ p.support) :
    ∃ a b, a ≠ b ∧ p.IsAttachment a ∧ p.IsAttachment b := by
  obtain ⟨z, a, hz, ha, hza⟩ :=
    hG.exists_adj_across (s := {w | w ∈ p.support}) hx p.start_mem_support
  have hau : a ≠ u := by
    rintro rfl
    exact hp.not_adj_start_of_forall_length_le hmax hz hza
  have hza_ne : z ≠ a := fun h ↦ hz (h ▸ ha)
  let z' : ({a}ᶜ : Set V) := ⟨z, by simp [hza_ne]⟩
  let u' : ({a}ᶜ : Set V) := ⟨u, by simp [hau.symm]⟩
  let s' : Set ({a}ᶜ : Set V) := {w | (w : V) ∈ p.support}
  have hz's : z' ∉ s' := hz
  have hu's : u' ∈ s' := p.start_mem_support
  obtain ⟨z₂, b₂, hz₂, hb₂, hz₂b₂⟩ :=
    (hdelete a).exists_adj_across (s := s') hz's hu's
  have hb₂_ne : (b₂ : V) ≠ a := by
    have hmem := b₂.property
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hmem
    exact hmem
  refine ⟨a, b₂, hb₂_ne.symm, ⟨ha, z, hz, hza⟩, ?_⟩
  refine ⟨hb₂, z₂, hz₂, ?_⟩
  exact hz₂b₂

/-- Two distinct attachment vertices of a longest path can be joined through
one or two outside vertices.  The resulting connector meets the original
path only at its endpoints. -/
lemma IsPath.exists_connector
    [DecidableEq V] (hp : p.IsPath) (hG : G.Connected)
    (hfour : G.NoIndependentFour)
    (hmax : ∀ (a b : V) (q : G.Walk a b), q.IsPath → q.length ≤ p.length)
    {a b : V} (hab : a ≠ b) (ha : p.IsAttachment a) (hb : p.IsAttachment b) :
    ∃ r : G.Walk a b, r.IsPath ∧ 2 ≤ r.length ∧
      ∀ z, z ∈ r.support → z ∈ p.support → z = a ∨ z = b := by
  obtain ⟨haP, x, hxP, hxa⟩ := ha
  obtain ⟨hbP, y, hyP, hyb⟩ := hb
  by_cases hxy : x = y
  · subst y
    have hax : a ≠ x := fun h ↦ hxP (h ▸ haP)
    have hxb : x ≠ b := fun h ↦ hxP (h ▸ hbP)
    let r : G.Walk a b := Walk.cons hxa.symm hyb.toWalk
    have hr : r.IsPath := by
      dsimp only [r]
      rw [isPath_def]
      simp [hab, hax, hxb]
    refine ⟨r, hr, by simp [r], ?_⟩
    intro z hz hzP
    simp [r] at hz
    rcases hz with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact (hxP hzP).elim
    · exact Or.inr rfl
  · have hxyAdj : G.Adj x y :=
      hp.adj_of_not_mem_support_of_not_mem_support hG hfour hmax hxP hyP hxy
    have hax : a ≠ x := fun h ↦ hxP (h ▸ haP)
    have hay : a ≠ y := fun h ↦ hyP (h ▸ haP)
    have hxb : x ≠ b := fun h ↦ hxP (h ▸ hbP)
    have hyb_ne : y ≠ b := fun h ↦ hyP (h ▸ hbP)
    let r : G.Walk a b := Walk.cons hxa.symm (Walk.cons hxyAdj hyb.toWalk)
    have hr : r.IsPath := by
      dsimp only [r]
      rw [isPath_def]
      simp [hab, hax, hay, hxb, hyb_ne, hxy]
    refine ⟨r, hr, by simp [r], ?_⟩
    intro z hz hzP
    simp [r] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact (hxP hzP).elim
    · exact (hyP hzP).elim
    · exact Or.inr rfl

/-- Splice a connector between positions `i < j` of a path, retaining the
prefix through `i` and the suffix from `j`. -/
lemma IsPath.splice_connector
    (hp : p.IsPath) {i j : ℕ} (hij : i < j) (hj : j ≤ p.length)
    {r : G.Walk (p.getVert i) (p.getVert j)} (hr : r.IsPath)
    (hrP : ∀ z, z ∈ r.support → z ∈ p.support →
      z = p.getVert i ∨ z = p.getVert j) :
    (((p.segment 0 i (by omega)).append r).append
      (p.segment j p.length hj)).IsPath := by
  let pre := p.segment 0 i (by omega)
  let suf := p.segment j p.length hj
  have hpre : pre.IsPath := hp.segment _
  have hsuf : suf.IsPath := hp.segment _
  have hpreP : pre.support ⊆ p.support := segment_support_subset _ _
  have hsufP : suf.support ⊆ p.support := segment_support_subset _ _
  have hpr : (pre.append r).IsPath := by
    apply hpre.append_of_forall_mem hr
    intro z hzpre hzr
    rcases hrP z hzr (hpreP hzpre) with hzi | hzj
    · exact hzi
    · obtain ⟨k, hk0, hki, hkz⟩ :=
        (mem_segment_support_iff hp (by omega) (by omega)).mp hzpre
      have hkj : p.getVert k = p.getVert j := hkz.trans hzj
      have := hp.getVert_injOn
        (show k ∈ {n | n ≤ p.length} by simpa using le_trans hki (le_trans hij.le hj))
        (show j ∈ {n | n ≤ p.length} by simpa using hj) hkj
      omega
  apply hpr.append_of_forall_mem hsuf
  intro z hzpr hzsuf
  rw [mem_support_append_iff] at hzpr
  rcases hzpr with hzpre | hzr
  · obtain ⟨k, hk0, hki, hkz⟩ :=
      (mem_segment_support_iff hp (by omega) (by omega)).mp hzpre
    obtain ⟨l, hjl, hlL, hlz⟩ :=
      (mem_segment_support_iff hp hj le_rfl).mp hzsuf
    have hkl : p.getVert k = p.getVert l := hkz.trans hlz.symm
    have := hp.getVert_injOn
      (show k ∈ {n | n ≤ p.length} by simpa using le_trans hki (le_trans hij.le hj))
      (show l ∈ {n | n ≤ p.length} by simpa using hlL) hkl
    omega
  · rcases hrP z hzr (hsufP hzsuf) with hzi | hzj
    · obtain ⟨l, hjl, hlL, hlz⟩ :=
        (mem_segment_support_iff hp hj le_rfl).mp hzsuf
      have hil : p.getVert i = p.getVert l := hzi.symm.trans hlz.symm
      have := hp.getVert_injOn
        (show i ∈ {n | n ≤ p.length} by
          simpa using le_trans hij.le hj)
        (show l ∈ {n | n ≤ p.length} by simpa using hlL) hil
      omega
    · exact hzj

lemma splice_connector_length
    (p : G.Walk u v) {i j : ℕ} (hij : i < j) (hj : j ≤ p.length)
    (r : G.Walk (p.getVert i) (p.getVert j)) :
    (((p.segment 0 i (by omega)).append r).append
      (p.segment j p.length hj)).length =
      i + r.length + (p.length - j) := by
  have hi : i ≤ p.length := le_trans hij.le hj
  rw [length_append, length_append, segment_length _ (by omega) hi,
    segment_length _ hj le_rfl]
  simp

lemma IsPath.middle_disjoint_splice
    (hp : p.IsPath) {i j : ℕ} (hgap : i + 2 ≤ j) (hj : j ≤ p.length)
    {r : G.Walk (p.getVert i) (p.getVert j)}
    (hrP : ∀ z, z ∈ r.support → z ∈ p.support →
      z = p.getVert i ∨ z = p.getVert j) :
    (p.segment (i + 1) (j - 1) (by omega)).support.Disjoint
      (((p.segment 0 i (by omega)).append r).append
        (p.segment j p.length hj)).support := by
  rw [List.disjoint_iff_ne]
  intro z hzmid w hws hzw
  subst w
  obtain ⟨k, hik, hkj, hkz⟩ :=
    (mem_segment_support_iff hp (by omega) (by omega)).mp hzmid
  rw [mem_support_append_iff, mem_support_append_iff] at hws
  rcases hws with (hzpre | hzr) | hzsuf
  · obtain ⟨l, hl0, hli, hlz⟩ :=
      (mem_segment_support_iff hp (by omega) (by omega)).mp hzpre
    have hkl : p.getVert k = p.getVert l := hkz.trans hlz.symm
    have := hp.getVert_injOn
      (show k ∈ {n | n ≤ p.length} by
        simp only [Set.mem_setOf_eq]; omega)
      (show l ∈ {n | n ≤ p.length} by
        simp only [Set.mem_setOf_eq]; omega) hkl
    omega
  · have hzP : z ∈ p.support :=
      segment_support_subset p (by omega) hzmid
    rcases hrP z hzr hzP with hzi | hzj
    · have hki : p.getVert k = p.getVert i := hkz.trans hzi
      have := hp.getVert_injOn
        (show k ∈ {n | n ≤ p.length} by
          simp only [Set.mem_setOf_eq]; omega)
        (show i ∈ {n | n ≤ p.length} by
          simp only [Set.mem_setOf_eq]; omega) hki
      omega
    · have hkj' : p.getVert k = p.getVert j := hkz.trans hzj
      have := hp.getVert_injOn
        (show k ∈ {n | n ≤ p.length} by
          simp only [Set.mem_setOf_eq]; omega)
        (show j ∈ {n | n ≤ p.length} by
          simp only [Set.mem_setOf_eq]; omega) hkj'
      omega
  · obtain ⟨l, hjl, hlL, hlz⟩ :=
      (mem_segment_support_iff hp hj le_rfl).mp hzsuf
    have hkl : p.getVert k = p.getVert l := hkz.trans hlz.symm
    have := hp.getVert_injOn
      (show k ∈ {n | n ≤ p.length} by
        simp only [Set.mem_setOf_eq]; omega)
      (show l ∈ {n | n ≤ p.length} by
        simp only [Set.mem_setOf_eq]; omega) hkl
    omega

/-- Core contradiction for the longest-path proof. -/
lemma IsPath.not_exists_not_mem_support
    [Fintype V] [DecidableEq V] (hp : p.IsPath) (hG : G.Connected)
    (hdelete : G.VertexDeletionConnected) (hfour : G.NoIndependentFour)
    (hmax : ∀ (a b : V) (q : G.Walk a b), q.IsPath → q.length ≤ p.length) :
    ¬∃ x, x ∉ p.support := by
  rintro ⟨x₀, hx₀⟩
  classical
  obtain ⟨z₁, z₂, hz₁z₂, hz₁, hz₂⟩ :=
    hp.exists_two_attachments hG hdelete hmax hx₀
  obtain ⟨i₁, hi₁z, hi₁L⟩ := mem_support_iff_exists_getVert.mp hz₁.1
  obtain ⟨i₂, hi₂z, hi₂L⟩ := mem_support_iff_exists_getVert.mp hz₂.1
  have hi₁i₂ : i₁ ≠ i₂ := by
    intro h
    apply hz₁z₂
    rw [← hi₁z, ← hi₂z, h]
  let A : Finset ℕ :=
    (Finset.range (p.length + 1)).filter
      (fun i ↦ p.IsAttachment (p.getVert i))
  have hi₁A : i₁ ∈ A := by
    simp only [A, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by simpa [hi₁z] using hz₁⟩
  have hi₂A : i₂ ∈ A := by
    simp only [A, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by simpa [hi₂z] using hz₂⟩
  have hA : A.Nonempty := ⟨i₁, hi₁A⟩
  let i := A.min' hA
  have hiA : i ∈ A := A.min'_mem hA
  have hAe : (A.erase i).Nonempty := by
    by_cases h : i₁ = i
    · exact ⟨i₂, Finset.mem_erase.mpr ⟨by omega, hi₂A⟩⟩
    · exact ⟨i₁, Finset.mem_erase.mpr ⟨h, hi₁A⟩⟩
  let j := (A.erase i).min' hAe
  have hjAe : j ∈ A.erase i := (A.erase i).min'_mem hAe
  have hjA : j ∈ A := Finset.mem_of_mem_erase hjAe
  have hij_ne : i ≠ j := by
    exact (Finset.ne_of_mem_erase hjAe).symm
  have hij_le : i ≤ j := A.min'_le j hjA
  have hij : i < j := lt_of_le_of_ne hij_le hij_ne
  have hconsecutive : ∀ k, i < k → k < j → k ∉ A := by
    intro k hik hkj hkA
    have hkAe : k ∈ A.erase i := Finset.mem_erase.mpr ⟨by omega, hkA⟩
    have := (A.erase i).min'_le k hkAe
    omega
  obtain ⟨hiRange, hiAtt⟩ := Finset.mem_filter.mp hiA
  obtain ⟨hjRange, hjAtt⟩ := Finset.mem_filter.mp hjA
  have hiL : i ≤ p.length := by
    simpa [Finset.mem_range] using hiRange
  have hjL : j ≤ p.length := by
    simpa [Finset.mem_range] using hjRange
  have hi0 : 0 < i := by
    obtain ⟨-, xi, hxiP, hxii⟩ := hiAtt
    by_contra hi
    have hiEq : i = 0 := by omega
    have hxii' := hxii
    rw [hiEq, getVert_zero] at hxii'
    exact hp.not_adj_start_of_forall_length_le hmax hxiP hxii'
  have hjLt : j < p.length := by
    obtain ⟨-, xj, hxjP, hxjj⟩ := hjAtt
    by_contra hj
    have hjEq : j = p.length := by omega
    have hxjj' := hxjj
    rw [hjEq, getVert_length] at hxjj'
    exact hp.not_adj_end_of_forall_length_le hmax hxjP hxjj'.symm
  have hnoAtt : ∀ k, i < k → k < j →
      ¬∃ y, y ∉ p.support ∧ G.Adj y (p.getVert k) := by
    intro k hik hkj hk
    apply hconsecutive k hik hkj
    simp only [A, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    exact ⟨getVert_mem_support p k, hk⟩
  obtain ⟨r, hr, hrlen, hrP⟩ :=
    hp.exists_connector hG hfour hmax
      (by
        intro h
        exact hij_ne (hp.getVert_injOn
          (show i ∈ {n | n ≤ p.length} by simpa using hiL)
          (show j ∈ {n | n ≤ p.length} by simpa using hjL) h))
      hiAtt hjAtt
  have hsplice :=
    hp.splice_connector hij hjL hr hrP
  have hgap : i + 2 ≤ j := by
    by_contra hgap
    have hji : j = i + 1 := by omega
    have hlenSplice :=
      splice_connector_length p hij hjL r
    have hle := hmax _ _ _ hsplice
    omega
  -- The two remaining reroutings show the crossed endpoint chords.
  have hsL : ¬G.Adj u (p.getVert (i + 1)) := by
    intro hus
    let mid := p.segment (i + 1) (j - 1) (by omega)
    let qRaw := ((p.segment 0 i (by omega)).append r).append
      (p.segment j p.length hjL)
    let q : G.Walk u v :=
      qRaw.copy (getVert_zero p) (getVert_length p)
    have hqPath : q.IsPath := by
      simpa [q, qRaw] using hsplice
    have hmid : mid.IsPath := hp.segment _
    have huMid : u ∉ mid.support := by
      intro hu
      obtain ⟨k, hik, hkj, hku⟩ :=
        (mem_segment_support_iff hp (by omega) (by omega)).mp hu
      have hk0 : p.getVert k = p.getVert 0 := by simpa using hku
      have := hp.getVert_injOn
        (show k ∈ {n | n ≤ p.length} by
          simp only [Set.mem_setOf_eq]; omega)
        (show 0 ∈ {n | n ≤ p.length} by simp) hk0
      omega
    have huMidRev : u ∉ mid.reverse.support := by
      simpa using huMid
    have hleft : (mid.reverse.concat hus.symm).IsPath :=
      hmid.reverse.concat huMidRev hus.symm
    have hdis : mid.support.Disjoint q.support := by
      simpa [q, qRaw] using hp.middle_disjoint_splice hgap hjL hrP
    have hlong : ((mid.reverse.concat hus.symm).append q).IsPath := by
      apply hleft.append_of_forall_mem hqPath
      intro z hzleft hzq
      have hz : z ∈ mid.reverse.support ∨ z = u := by
        simpa using hzleft
      rcases hz with hzmid | hzu
      · have hzmid' : z ∈ mid.support := by simpa using hzmid
        exact (hdis hzmid' hzq).elim
      · exact hzu
    have hmidLen : mid.length = (j - 1) - (i + 1) :=
      segment_length p (by omega) (by omega)
    have hqLen : q.length = i + r.length + (p.length - j) :=
      by simpa [q, qRaw] using splice_connector_length p hij hjL r
    have hle := hmax _ _ _ hlong
    simp only [length_append, length_concat] at hle
    rw [length_reverse, hmidLen, hqLen] at hle
    omega
  have hsR : G.Adj v (p.getVert (i + 1)) := by
    obtain ⟨-, xi, hxiP, hxii⟩ := hiAtt
    have huv : u ≠ v :=
      hp.start_ne_end_of_connected_of_forall_length_le hG hmax hx₀
    have hux : u ≠ xi := fun h ↦ hxiP (h ▸ p.start_mem_support)
    have hus : u ≠ p.getVert (i + 1) := by
      intro h
      have h' : p.getVert 0 = p.getVert (i + 1) := by simpa using h
      have := hp.getVert_injOn
        (show 0 ∈ {n | n ≤ p.length} by simp)
        (show i + 1 ∈ {n | n ≤ p.length} by
          simp only [Set.mem_setOf_eq]; omega) h'
      omega
    have hvx : v ≠ xi := fun h ↦ hxiP (h ▸ p.end_mem_support)
    have hvs : v ≠ p.getVert (i + 1) := by
      intro h
      have h' : p.getVert p.length = p.getVert (i + 1) := by
        simpa using h
      have := hp.getVert_injOn
        (show p.length ∈ {n | n ≤ p.length} by simp)
        (show i + 1 ∈ {n | n ≤ p.length} by
          simp only [Set.mem_setOf_eq]; omega) h'
      omega
    have hxs : xi ≠ p.getVert (i + 1) :=
      fun h ↦ hxiP (h ▸ getVert_mem_support p (i + 1))
    have hnuv : ¬G.Adj u v :=
      hp.not_adj_endpoints_of_connected_of_forall_length_le hG hmax hx₀
    have hnux : ¬G.Adj u xi := by
      rw [G.adj_comm]
      exact hp.not_adj_start_of_forall_length_le hmax hxiP
    have hnvx : ¬G.Adj v xi :=
      hp.not_adj_end_of_forall_length_le hmax hxiP
    have hnxs : ¬G.Adj xi (p.getVert (i + 1)) := by
      intro h
      exact hnoAtt (i + 1) (by omega) (by omega) ⟨xi, hxiP, h⟩
    rcases hfour huv hux hus hvx hvs hxs with
      huv' | hux' | hus' | hvx' | hvs' | hxs'
    · exact (hnuv huv').elim
    · exact (hnux hux').elim
    · exact (hsL hus').elim
    · exact (hnvx hvx').elim
    · exact hvs'
    · exact (hnxs hxs').elim
  have htR : ¬G.Adj v (p.getVert (j - 1)) := by
    intro hvt
    let mid := p.segment (i + 1) (j - 1) (by omega)
    let qRaw := ((p.segment 0 i (by omega)).append r).append
      (p.segment j p.length hjL)
    let q : G.Walk u v :=
      qRaw.copy (getVert_zero p) (getVert_length p)
    have hqPath : q.IsPath := by
      simpa [q, qRaw] using hsplice
    have hmid : mid.IsPath := hp.segment _
    have hvMid : v ∉ mid.support := by
      intro hv
      obtain ⟨k, hik, hkj, hkv⟩ :=
        (mem_segment_support_iff hp (by omega) (by omega)).mp hv
      have hkL : p.getVert k = p.getVert p.length := by simpa using hkv
      have := hp.getVert_injOn
        (show k ∈ {n | n ≤ p.length} by
          simp only [Set.mem_setOf_eq]; omega)
        (show p.length ∈ {n | n ≤ p.length} by simp) hkL
      omega
    have hleft : (mid.concat hvt.symm).IsPath :=
      hmid.concat hvMid hvt.symm
    have hdis : mid.support.Disjoint q.support := by
      simpa [q, qRaw] using hp.middle_disjoint_splice hgap hjL hrP
    have hlong : ((mid.concat hvt.symm).append q.reverse).IsPath := by
      apply hleft.append_of_forall_mem hqPath.reverse
      intro z hzleft hzq
      have hz : z ∈ mid.support ∨ z = v := by
        simpa using hzleft
      rcases hz with hzmid | hzv
      · have hzq' : z ∈ q.support := by simpa using hzq
        exact (hdis hzmid hzq').elim
      · exact hzv
    have hmidLen : mid.length = (j - 1) - (i + 1) :=
      segment_length p (by omega) (by omega)
    have hqLen : q.length = i + r.length + (p.length - j) :=
      by simpa [q, qRaw] using splice_connector_length p hij hjL r
    have hle := hmax _ _ _ hlong
    simp only [length_append, length_concat, length_reverse] at hle
    rw [hmidLen, hqLen] at hle
    omega
  have htL : G.Adj u (p.getVert (j - 1)) := by
    obtain ⟨-, xj, hxjP, hxjj⟩ := hjAtt
    have huv : u ≠ v :=
      hp.start_ne_end_of_connected_of_forall_length_le hG hmax hx₀
    have hux : u ≠ xj := fun h ↦ hxjP (h ▸ p.start_mem_support)
    have hut : u ≠ p.getVert (j - 1) := by
      intro h
      have h' : p.getVert 0 = p.getVert (j - 1) := by simpa using h
      have := hp.getVert_injOn
        (show 0 ∈ {n | n ≤ p.length} by simp)
        (show j - 1 ∈ {n | n ≤ p.length} by
          simp only [Set.mem_setOf_eq]; omega) h'
      omega
    have hvx : v ≠ xj := fun h ↦ hxjP (h ▸ p.end_mem_support)
    have hvt : v ≠ p.getVert (j - 1) := by
      intro h
      have h' : p.getVert p.length = p.getVert (j - 1) := by
        simpa using h
      have := hp.getVert_injOn
        (show p.length ∈ {n | n ≤ p.length} by simp)
        (show j - 1 ∈ {n | n ≤ p.length} by
          simp only [Set.mem_setOf_eq]; omega) h'
      omega
    have hxt : xj ≠ p.getVert (j - 1) :=
      fun h ↦ hxjP (h ▸ getVert_mem_support p (j - 1))
    have hnuv : ¬G.Adj u v :=
      hp.not_adj_endpoints_of_connected_of_forall_length_le hG hmax hx₀
    have hnux : ¬G.Adj u xj := by
      rw [G.adj_comm]
      exact hp.not_adj_start_of_forall_length_le hmax hxjP
    have hnvx : ¬G.Adj v xj :=
      hp.not_adj_end_of_forall_length_le hmax hxjP
    have hnxt : ¬G.Adj xj (p.getVert (j - 1)) := by
      intro h
      exact hnoAtt (j - 1) (by omega) (by omega) ⟨xj, hxjP, h⟩
    rcases hfour huv hux hut hvx hvt hxt with
      huv' | hux' | hut' | hvx' | hvt' | hxt'
    · exact (hnuv huv').elim
    · exact (hnux hux').elim
    · exact hut'
    · exact (hnvx hvx').elim
    · exact (htR hvt').elim
    · exact (hnxt hxt').elim
  -- The final rerouting uses `r`, the suffix, the middle segment, and
  -- the prefix, contradicting maximality.
  let sufRaw := p.segment j p.length hjL
  let suf : G.Walk (p.getVert j) v :=
    sufRaw.copy rfl (getVert_length p)
  let mid := p.segment (i + 1) (j - 1) (by omega)
  let preRaw := p.segment 0 (i - 1) (by omega)
  let pre : G.Walk u (p.getVert (i - 1)) :=
    preRaw.copy (getVert_zero p) rfl
  have hsuf : suf.IsPath := by
    simpa [suf, sufRaw] using hp.segment hjL
  have hmid : mid.IsPath := hp.segment _
  have hpre : pre.IsPath := by
    simpa [pre, preRaw] using hp.segment (show 0 ≤ i - 1 by omega)
  have hsufMem : ∀ {z}, z ∈ suf.support ↔
      ∃ k, j ≤ k ∧ k ≤ p.length ∧ p.getVert k = z := by
    intro z
    simpa [suf, sufRaw] using
      (mem_segment_support_iff hp hjL le_rfl (z := z))
  have hsufP : suf.support ⊆ p.support := by
    intro z hz
    apply segment_support_subset p hjL
    simpa [suf, sufRaw] using hz
  have hpreMem : ∀ {z}, z ∈ pre.support ↔
      ∃ k, 0 ≤ k ∧ k ≤ i - 1 ∧ p.getVert k = z := by
    intro z
    simpa [pre, preRaw] using
      (mem_segment_support_iff hp
        (show 0 ≤ i - 1 by omega) (show i - 1 ≤ p.length by omega)
        (z := z))
  have hpreP : pre.support ⊆ p.support := by
    intro z hz
    apply segment_support_subset p (show 0 ≤ i - 1 by omega)
    simpa [pre, preRaw] using hz
  have hpi_ne_pj : p.getVert i ≠ p.getVert j := by
    intro h
    exact hij_ne (hp.getVert_injOn
      (show i ∈ {n | n ≤ p.length} by simpa using hiL)
      (show j ∈ {n | n ≤ p.length} by simpa using hjL) h)
  have hrs : (r.append suf).IsPath := by
    apply hr.append_of_forall_mem hsuf
    intro z hzr hzsuf
    have hzP : z ∈ p.support := hsufP hzsuf
    rcases hrP z hzr hzP with hzi | hzj
    · obtain ⟨k, hjk, hkL, hkz⟩ :=
        hsufMem.mp hzsuf
      have hik : p.getVert i = p.getVert k := hzi.symm.trans hkz.symm
      have := hp.getVert_injOn
        (show i ∈ {n | n ≤ p.length} by simpa using hiL)
        (show k ∈ {n | n ≤ p.length} by simpa using hkL) hik
      omega
    · exact hzj
  have hsNotRS : p.getVert (i + 1) ∉ (r.append suf).support := by
    intro hs
    rw [mem_support_append_iff] at hs
    rcases hs with hsr | hssuf
    · rcases hrP _ hsr (getVert_mem_support p (i + 1)) with hsi | hsj
      · have := hp.getVert_injOn
          (show i + 1 ∈ {n | n ≤ p.length} by
            simp only [Set.mem_setOf_eq]; omega)
          (show i ∈ {n | n ≤ p.length} by simpa using hiL) hsi
        omega
      · have := hp.getVert_injOn
          (show i + 1 ∈ {n | n ≤ p.length} by
            simp only [Set.mem_setOf_eq]; omega)
          (show j ∈ {n | n ≤ p.length} by simpa using hjL) hsj
        omega
    · obtain ⟨k, hjk, hkL, hks⟩ :=
        hsufMem.mp hssuf
      have := hp.getVert_injOn
        (show k ∈ {n | n ≤ p.length} by simpa using hkL)
        (show i + 1 ∈ {n | n ≤ p.length} by
          simp only [Set.mem_setOf_eq]; omega) hks
      omega
  have hrsS : ((r.append suf).concat hsR).IsPath :=
    hrs.concat hsNotRS hsR
  have hmidDisj :
      mid.support.Disjoint (r.append suf).support := by
    rw [List.disjoint_iff_ne]
    intro z hzmid w hrs' hzw
    subst w
    obtain ⟨k, hik, hkj, hkz⟩ :=
      (mem_segment_support_iff hp (by omega) (by omega)).mp hzmid
    rw [mem_support_append_iff] at hrs'
    rcases hrs' with hzr | hzsuf
    · have hzP : z ∈ p.support :=
        segment_support_subset p (by omega) hzmid
      rcases hrP z hzr hzP with hzi | hzj
      · have hki : p.getVert k = p.getVert i := hkz.trans hzi
        have := hp.getVert_injOn
          (show k ∈ {n | n ≤ p.length} by
            simp only [Set.mem_setOf_eq]; omega)
          (show i ∈ {n | n ≤ p.length} by simpa using hiL) hki
        omega
      · have hkj' : p.getVert k = p.getVert j := hkz.trans hzj
        have := hp.getVert_injOn
          (show k ∈ {n | n ≤ p.length} by
            simp only [Set.mem_setOf_eq]; omega)
          (show j ∈ {n | n ≤ p.length} by simpa using hjL) hkj'
        omega
    · obtain ⟨l, hjl, hlL, hlz⟩ :=
        hsufMem.mp hzsuf
      have hkl : p.getVert k = p.getVert l := hkz.trans hlz.symm
      have := hp.getVert_injOn
        (show k ∈ {n | n ≤ p.length} by
          simp only [Set.mem_setOf_eq]; omega)
        (show l ∈ {n | n ≤ p.length} by simpa using hlL) hkl
      omega
  have hrsSMid : (((r.append suf).concat hsR).append mid).IsPath := by
    apply hrsS.append_of_forall_mem hmid
    intro z hzleft hzmid
    have hz : z ∈ (r.append suf).support ∨ z = p.getVert (i + 1) := by
      simpa using hzleft
    rcases hz with hzrs | hzs
    · exact (hmidDisj hzmid hzrs).elim
    · exact hzs
  have huPos : ∀ k, 0 < k → k ≤ p.length → p.getVert k ≠ u := by
    intro k hk0 hkL hku
    have hk : p.getVert k = p.getVert 0 := by simpa using hku
    have := hp.getVert_injOn
      (show k ∈ {n | n ≤ p.length} by simpa using hkL)
      (show 0 ∈ {n | n ≤ p.length} by simp) hk
    omega
  have huLeft : u ∉ (((r.append suf).concat hsR).append mid).support := by
    intro hu
    rw [mem_support_append_iff] at hu
    rcases hu with huRSs | huMid
    · have hu' : u ∈ (r.append suf).support ∨ u = p.getVert (i + 1) := by
        simpa using huRSs
      rcases hu' with huRS | hus
      · rw [mem_support_append_iff] at huRS
        rcases huRS with hur | husuf
        · rcases hrP u hur p.start_mem_support with hui | huj
          · exact huPos i hi0 hiL hui.symm
          · exact huPos j (by omega) hjL huj.symm
        · obtain ⟨k, hjk, hkL, hku⟩ :=
            hsufMem.mp husuf
          exact huPos k (by omega) hkL hku
      · exact huPos (i + 1) (by omega) (by omega) hus.symm
    · obtain ⟨k, hik, hkj, hku⟩ :=
        (mem_segment_support_iff hp (by omega) (by omega)).mp huMid
      exact huPos k (by omega) (by omega) hku
  have hthroughU :
      ((((r.append suf).concat hsR).append mid).concat htL.symm).IsPath :=
    hrsSMid.concat huLeft htL.symm
  have hfinal :
      (((((r.append suf).concat hsR).append mid).concat htL.symm).append pre).IsPath := by
    apply hthroughU.append_of_forall_mem hpre
    intro z hzleft hzpre
    have hz : z ∈ (((r.append suf).concat hsR).append mid).support ∨ z = u := by
      simpa using hzleft
    rcases hz with hzcore | hzu
    · obtain ⟨l, hl0, hli, hlz⟩ :=
        hpreMem.mp hzpre
      rw [mem_support_append_iff] at hzcore
      rcases hzcore with hzRSs | hzmid
      · have hz' : z ∈ (r.append suf).support ∨ z = p.getVert (i + 1) := by
          simpa using hzRSs
        rcases hz' with hzRS | hzs
        · rw [mem_support_append_iff] at hzRS
          rcases hzRS with hzr | hzsuf
          · have hzP : z ∈ p.support := hpreP hzpre
            rcases hrP z hzr hzP with hzi | hzj
            · have hil : p.getVert i = p.getVert l := hzi.symm.trans hlz.symm
              have := hp.getVert_injOn
                (show i ∈ {n | n ≤ p.length} by simpa using hiL)
                (show l ∈ {n | n ≤ p.length} by
                  simp only [Set.mem_setOf_eq]; omega) hil
              omega
            · have hjl : p.getVert j = p.getVert l := hzj.symm.trans hlz.symm
              have := hp.getVert_injOn
                (show j ∈ {n | n ≤ p.length} by simpa using hjL)
                (show l ∈ {n | n ≤ p.length} by
                  simp only [Set.mem_setOf_eq]; omega) hjl
              omega
          · obtain ⟨k, hjk, hkL, hkz⟩ :=
              hsufMem.mp hzsuf
            have hkl : p.getVert k = p.getVert l := hkz.trans hlz.symm
            have := hp.getVert_injOn
              (show k ∈ {n | n ≤ p.length} by simpa using hkL)
              (show l ∈ {n | n ≤ p.length} by
                simp only [Set.mem_setOf_eq]; omega) hkl
            omega
        · have hsl : p.getVert (i + 1) = p.getVert l :=
            hzs.symm.trans hlz.symm
          have := hp.getVert_injOn
            (show i + 1 ∈ {n | n ≤ p.length} by
              simp only [Set.mem_setOf_eq]; omega)
            (show l ∈ {n | n ≤ p.length} by
              simp only [Set.mem_setOf_eq]; omega) hsl
          omega
      · obtain ⟨k, hik, hkj, hkz⟩ :=
          (mem_segment_support_iff hp (by omega) (by omega)).mp hzmid
        have hkl : p.getVert k = p.getVert l := hkz.trans hlz.symm
        have := hp.getVert_injOn
          (show k ∈ {n | n ≤ p.length} by
            simp only [Set.mem_setOf_eq]; omega)
          (show l ∈ {n | n ≤ p.length} by
            simp only [Set.mem_setOf_eq]; omega) hkl
        omega
    · exact hzu
  have hsufLen : suf.length = p.length - j :=
    by simp [suf, sufRaw]
  have hmidLen : mid.length = (j - 1) - (i + 1) :=
    segment_length p (by omega) (by omega)
  have hpreLen : pre.length = (i - 1) :=
    by simpa only [pre, preRaw, length_copy] using
      segment_length p (show 0 ≤ i - 1 by omega) (by omega)
  have hle := hmax _ _ _ hfinal
  simp only [length_append, length_concat] at hle
  rw [hsufLen, hmidLen, hpreLen] at hle
  omega

end Walk

/-- A finite connected graph remains traceable when deleting any one vertex
leaves it connected and it has no independent set of four vertices.

This is the public wrapper around the longest-path rerouting argument. -/
theorem exists_hamiltonianPath_of_vertexDeletionConnected_of_noIndependentFour
    [Fintype V] [DecidableEq V] (hG : G.Connected)
    (hdelete : G.VertexDeletionConnected) (hfour : G.NoIndependentFour) :
    ∃ u v, ∃ p : G.Walk u v, p.IsHamiltonian := by
  letI : Nonempty V := hG.nonempty
  obtain ⟨u, v, p, hp, hmax⟩ :=
    Walk.exists_isPath_forall_isPath_length_le_length G
  have hnone : ¬∃ x, x ∉ p.support :=
    hp.not_exists_not_mem_support hG hdelete hfour hmax
  have hall : ∀ x, x ∈ p.support := by
    intro x
    by_contra hx
    exact hnone ⟨x, hx⟩
  exact ⟨u, v, p, hp.isHamiltonian_of_mem hall⟩

end SimpleGraph
