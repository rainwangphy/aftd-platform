import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphRotationFacePerm

/-!
# simple_graph_diagonal_conflict_graph

Topic: combinatorics   Node: 64fa2be8d3b7

Provenance: formalization of a published result. Source: arXiv:2611.18384 Section 2.2 and line 298

Given a simple graph G on Fin n and a permutation σ of G.Dart, simple_graph_diagonal_conflict_graph G σ defines the simple graph on Fin n where vertices x and y are adjacent if and only if x ≠ y and either G.Adj x y or there exists a dart d of G such that x = ((simple_graph_rotation_face_perm G σ)^[2] d).fst and y = ((simple_graph_rotation_face_perm G σ)^[2] d.symm).fst.
-/

/-- The diagonal conflict graph D(T) obtained by adding diagonal edges between diagonally adjacent vertices. -/
def simple_graph_diagonal_conflict_graph {n : ℕ} (G : SimpleGraph (Fin n))
    (σ : Equiv.Perm G.Dart) : SimpleGraph (Fin n) where
  Adj x y := x ≠ y ∧ (G.Adj x y ∨
    ∃ d : G.Dart,
      x = ((simple_graph_rotation_face_perm G σ)^[2] d).fst ∧
      y = ((simple_graph_rotation_face_perm G σ)^[2] d.symm).fst)
  symm := ⟨by
    intro x y ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with h_adj | ⟨d, hx, hy⟩
    · exact Or.inl h_adj.symm
    · refine Or.inr ⟨d.symm, ?_⟩
      rw [d.symm_symm]
      exact ⟨hy, hx⟩⟩
  loopless := ⟨by
    intro x ⟨hne, _⟩
    exact hne rfl⟩
