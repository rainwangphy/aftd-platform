import AFTD.Prelude

/-!
# cartesian_product_complete_graphs

Topic: graphs   Node: 5a5eb086f101

Provenance: formalization of a published result. Source: arXiv:2611.03956, Definition 2.6

The Cartesian product of t complete graphs with sizes given by a : Fin t → ℕ, defined as a simple graph on vertex type (i : Fin t) → Fin (a i), where two vertices are adjacent if and only if they differ in exactly one coordinate.
-/

/-- Cartesian product of t complete graphs with vertex set (i : Fin t) → Fin (a i). -/
def cartesian_product_complete_graphs {t : ℕ} (a : Fin t → ℕ) :
    SimpleGraph ((i : Fin t) → Fin (a i)) := by
  refine SimpleGraph.mk (fun u v => ∃ j : Fin t, u j ≠ v j ∧ ∀ i : Fin t, i ≠ j → u i = v i) ?_ ?_
  · exact Std.Symm.mk (by
      intro u v ⟨j, hj, hrest⟩
      exact ⟨j, hj.symm, fun i hi => (hrest i hi).symm⟩)
  · exact Std.Irrefl.mk (by
      intro u ⟨j, hj, _⟩
      exact hj rfl)
