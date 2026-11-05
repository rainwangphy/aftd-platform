import AFTD.Prelude

/-!
# has_three_colored_anti_ramsey

Topic: combinatorics   Node: 7cbcfca4f895

Provenance: formalization of a published result. Source: arXiv:2611.03878, Definition 2.1

A complete graph on N vertices admits a three-colored anti-Ramsey edge-coloring for K_n if there exists an edge-coloring c : Sym2 (Fin N) → Fin 3 such that for every n-element subset s of vertices and every color col in Fin 3, there exist distinct vertices u, v in s whose connecting edge has color col.
-/

/-- The complete graph K_N admits a 3-edge-coloring such that every complete subgraph on n vertices contains all three colors. -/
def has_three_colored_anti_ramsey (N n : ℕ) : Prop :=
  ∃ c : Sym2 (Fin N) → Fin 3,
    ∀ s : Finset (Fin N), s.card = n →
      ∀ col : Fin 3, ∃ u ∈ s, ∃ v ∈ s, u ≠ v ∧ c s(u, v) = col
