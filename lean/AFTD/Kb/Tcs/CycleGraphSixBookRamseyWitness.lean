import AFTD.Prelude

/-!
# cycle_graph_six_book_ramsey_witness

Topic: combinatorics   Node: c35ba5d71b68

Provenance: formalization of a published result. Source: arXiv:2610.36522 Appendix A -- Constructions for Nearly Diagonal Book Ramsey Numbers

In the 6-cycle graph on Fin 6, every pair of adjacent vertices has at most 0 common neighbors, and every pair of distinct non-adjacent vertices has at most 1 common neighbor in the complement graph.
-/

/-- The 6-cycle C_6 satisfies the book Ramsey conditions for n=2 on 6 vertices: every adjacent pair has at most 0 common neighbors, and every distinct non-adjacent pair has at most 1 common neighbor in the complement. -/
theorem cycle_graph_six_book_ramsey_witness :
    (∀ u v : Fin 6, (SimpleGraph.cycleGraph 6).Adj u v → Fintype.card ((SimpleGraph.cycleGraph 6).commonNeighbors u v) ≤ 0) ∧
    (∀ u v : Fin 6, u ≠ v → ¬ (SimpleGraph.cycleGraph 6).Adj u v → Fintype.card ((SimpleGraph.cycleGraph 6)ᶜ.commonNeighbors u v) ≤ 1) := by
  decide
