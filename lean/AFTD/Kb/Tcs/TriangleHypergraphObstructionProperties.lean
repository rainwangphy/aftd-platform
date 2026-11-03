import AFTD.Prelude
import AFTD.Kb.Tcs.TriangleHypergraphObstruction

/-!
# triangle_hypergraph_obstruction_properties

Topic: graphs   Node: f86992068c29

Provenance: helper lemma. Finite obstruction to the linear degree-three hypergraph route for the triangle packing-cover problem; computed in experiment 13104. No novelty is claimed for this small plane-derived example.

The six given triples each have three points; distinct triples meet in exactly one point; no point is in more than three triples; no set of at most two points meets all triples; and a three-point cover exists. Thus the maximum packing has size one and the minimum cover size three, despite the system having fewer than seven edges.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem triangle_hypergraph_obstruction_properties :
    triangle_hypergraph_obstruction.card = 6 ∧
    (∀ e ∈ triangle_hypergraph_obstruction, e.card = 3) ∧
    (∀ e ∈ triangle_hypergraph_obstruction, ∀ f ∈ triangle_hypergraph_obstruction,
      e ≠ f → (e ∩ f).card = 1) ∧
    (∀ v : Fin 7, (triangle_hypergraph_obstruction.filter fun e => v ∈ e).card ≤ 3) ∧
    (∀ F : Finset (Fin 7), F.card ≤ 2 →
      ∃ e ∈ triangle_hypergraph_obstruction, Disjoint F e) ∧
    (∃ F : Finset (Fin 7), F.card = 3 ∧
      ∀ e ∈ triangle_hypergraph_obstruction, ¬ Disjoint F e) := by
  decide
