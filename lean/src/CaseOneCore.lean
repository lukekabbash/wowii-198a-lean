/- Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0 . -/

import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

/-!
# The list-to-walk step in WOWII Conjecture 198a

This file isolates the final combinatorial step of the `b = diameter + 1`
case.  Once the vertices have been arranged in a duplicate-free adjacency
chain, the chain is a Hamiltonian path.
-/

namespace WrittenOnTheWallII.GraphConjecture198a

open SimpleGraph

universe u

variable {α : Type u} [DecidableEq α] {G : SimpleGraph α}

/-- Convert a nonempty adjacency chain into a walk with exactly that support. -/
def walkOfAdjacencyChain (a : α) :
    (l : List α) → List.IsChain G.Adj (a :: l) →
      Σ b : α, {p : G.Walk a b // p.support = a :: l}
  | [], _ => ⟨a, ⟨.nil, rfl⟩⟩
  | b :: l, h =>
      let hab := (List.isChain_cons_cons.mp h).1
      let htail := (List.isChain_cons_cons.mp h).2
      let ⟨c, p, hp⟩ := walkOfAdjacencyChain b l htail
      ⟨c, ⟨.cons hab p, by simp only [Walk.support_cons, hp]⟩⟩

/--
A list which contains every vertex exactly once and whose consecutive entries
are adjacent determines a Hamiltonian path.
-/
theorem exists_hamiltonianPath_of_adjacencyChain [Fintype α]
    (a : α) (l : List α) (hchain : List.IsChain G.Adj (a :: l))
    (hnodup : (a :: l).Nodup) (hcover : ∀ x : α, x ∈ a :: l) :
    ∃ b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨b, p, hp⟩ := walkOfAdjacencyChain a l hchain
  refine ⟨b, p, ?_⟩
  apply Walk.IsPath.isHamiltonian_of_mem (Walk.IsPath.mk' ?_) ?_
  · simpa only [hp] using hnodup
  · intro x
    simpa only [hp] using hcover x

/--
Endpoint-free form matching the conclusion used in Conjecture 198a.
-/
theorem has_hamiltonianPath_of_vertex_order [Fintype α]
    (order : List α) (hne : order ≠ [])
    (hchain : List.IsChain G.Adj order) (hnodup : order.Nodup)
    (hcover : ∀ x : α, x ∈ order) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨b, p, hp⟩ :=
    exists_hamiltonianPath_of_adjacencyChain a l hchain hnodup hcover
  exact ⟨a, b, p, hp⟩

/--
The block form used in the `b = diameter + 1` argument.  A Hamiltonian
ordering can be assembled chunk-by-chunk: each chunk is an adjacency chain,
and the last vertex of every chunk is adjacent to the first vertex of the
next chunk.
-/
theorem has_hamiltonianPath_of_chunks [Fintype α]
    (chunks : List (List α)) (hchunks : chunks ≠ [])
    (hnonempty : [] ∉ chunks)
    (hwithin : ∀ l ∈ chunks, List.IsChain G.Adj l)
    (hbetween :
      chunks.IsChain fun l₁ l₂ =>
        ∀ᵉ (x ∈ l₁.getLast?) (y ∈ l₂.head?), G.Adj x y)
    (hnodup : chunks.flatten.Nodup)
    (hcover : ∀ x : α, x ∈ chunks.flatten) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  apply has_hamiltonianPath_of_vertex_order chunks.flatten
  · cases chunks with
    | nil => simp at hchunks
    | cons chunk chunks =>
        have hchunk : chunk ≠ [] := by
          intro h
          apply hnonempty
          simp [h]
        simp only [List.flatten_cons]
        exact List.append_ne_nil_of_left_ne_nil hchunk chunks.flatten
  · exact (List.isChain_flatten hnonempty).mpr ⟨hwithin, hbetween⟩
  · exact hnodup
  · exact hcover

omit [DecidableEq α] in
/--
Any duplicate-free list contained in a clique is an adjacency chain.
-/
theorem isChain_of_mem_clique
    (l : List α) (hnodup : l.Nodup)
    (hclique : ∀ ⦃x⦄, x ∈ l → ∀ ⦃y⦄, y ∈ l → x ≠ y → G.Adj x y) :
    List.IsChain G.Adj l := by
  apply List.Pairwise.isChain
  rw [List.pairwise_iff_get]
  intro i j hij
  apply hclique (List.get_mem l i) (List.get_mem l j)
  intro heq
  exact hij.ne (hnodup.injective_get heq)

omit [DecidableEq α] in
/--
Prepending a vertex adjacent to every member of a duplicate-free clique
preserves the adjacency-chain property.
-/
theorem isChain_cons_of_mem_clique
    (a : α) (l : List α) (hnodup : l.Nodup)
    (ha : ∀ x ∈ l, G.Adj a x)
    (hclique : ∀ ⦃x⦄, x ∈ l → ∀ ⦃y⦄, y ∈ l → x ≠ y → G.Adj x y) :
    List.IsChain G.Adj (a :: l) := by
  cases l with
  | nil => exact List.isChain_singleton a
  | cons x xs =>
      apply List.IsChain.cons_cons (ha x (by simp))
      exact isChain_of_mem_clique (x :: xs) hnodup hclique

/-- Turn an anchor and its following block into one chunk of the vertex order. -/
def anchoredChunk : α × List α → List α
  | (a, l) => a :: l

/--
Abstract form of the block-threading argument in the `b = diameter + 1`
case.  Every block is a clique, its anchor sees the entire block, and the
last point of a block sees the next anchor (the anchor-to-anchor edge handles
an empty block).  The remaining two hypotheses say that these blocks form a
partition of the vertex set.
-/
theorem has_hamiltonianPath_of_anchored_clique_blocks [Fintype α]
    (blocks : List (α × List α)) (hblocks : blocks ≠ [])
    (hlocal :
      ∀ s ∈ blocks,
        s.2.Nodup ∧
        (∀ x ∈ s.2, G.Adj s.1 x) ∧
        (∀ ⦃x⦄, x ∈ s.2 → ∀ ⦃y⦄, y ∈ s.2 → x ≠ y → G.Adj x y))
    (hsucc :
      blocks.IsChain fun s t =>
        G.Adj s.1 t.1 ∧ ∀ x ∈ s.2, G.Adj x t.1)
    (hnodup : (blocks.map anchoredChunk).flatten.Nodup)
    (hcover : ∀ x : α, x ∈ (blocks.map anchoredChunk).flatten) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  apply has_hamiltonianPath_of_chunks (blocks.map anchoredChunk)
  · cases blocks with
    | nil => exact (hblocks rfl).elim
    | cons s ss => simp
  · simp [anchoredChunk]
  · intro chunk hchunk
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hchunk
    obtain ⟨hnd, ha, hc⟩ := hlocal s hs
    rcases s with ⟨a, l⟩
    exact isChain_cons_of_mem_clique a l hnd ha hc
  · rw [List.isChain_map]
    apply hsucc.imp
    rintro ⟨a, l⟩ ⟨b, m⟩ ⟨hab, hlb⟩
    cases l with
    | nil => simpa [anchoredChunk] using hab
    | cons x xs =>
        change
          ∀ z ∈ (a :: x :: xs).getLast?,
            ∀ y ∈ (b :: m).head?, G.Adj z y
        intro z hz y hy
        have hby : b = y := by
          exact Option.some.inj hy
        subst y
        rw [List.getLast?_cons_cons] at hz
        obtain ⟨hne, rfl⟩ := List.mem_getLast?_eq_getLast hz
        exact hlb _ (List.getLast_mem hne)
  · exact hnodup
  · exact hcover

end WrittenOnTheWallII.GraphConjecture198a
