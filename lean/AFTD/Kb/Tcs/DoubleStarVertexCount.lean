import AFTD.Prelude

/-!
# double_star_vertex_count

Topic: graphs   Node: 111b03eb09a3

Provenance: helper lemma. arXiv:2611.15124 Section 1, Domination in token graphs of graphs with domination number two

The double star graph S_{a,b} on vertex type Bool ⊕ Fin a ⊕ Fin b has a + b + 2 vertices.
-/

/-- The double star S_{a,b} on Bool ⊕ Fin a ⊕ Fin b has a + b + 2 vertices. -/
theorem double_star_vertex_count (a b : ℕ) :
    Fintype.card (Bool ⊕ Fin a ⊕ Fin b) = a + b + 2 := by
  simp
  omega
