import AFTD.Prelude
import AFTD.Kb.Tcs.CycleGraphSixBookRamseyWitness

/-!
# book_ramsey_b1_b2_graph_exists

Topic: combinatorics   Node: fd865bda32ee

Provenance: formalization of a published result. Source: arXiv:2610.36522 Appendix A -- Constructions for Nearly Diagonal Book Ramsey Numbers

There exists a simple graph G on 6 vertices with decidable adjacency such that every pair of adjacent vertices has at most 0 common neighbors in G, and every pair of distinct non-adjacent vertices has at most 1 common neighbor in the complement graph Gᶜ.
-/

/-- Existence of a Ramsey (B_1, B_2; 6) graph on 6 vertices, establishing the base case n=2 of nearly diagonal book Ramsey lower bounds. -/
theorem book_ramsey_b1_b2_graph_exists :
    ∃ (G : SimpleGraph (Fin 6)) (_ : DecidableRel G.Adj),
      (∀ u v : Fin 6, G.Adj u v → Fintype.card (G.commonNeighbors u v) ≤ 0) ∧
      (∀ u v : Fin 6, u ≠ v → ¬ G.Adj u v → Fintype.card (Gᶜ.commonNeighbors u v) ≤ 1) :=
  ⟨SimpleGraph.cycleGraph 6, inferInstance, cycle_graph_six_book_ramsey_witness⟩
