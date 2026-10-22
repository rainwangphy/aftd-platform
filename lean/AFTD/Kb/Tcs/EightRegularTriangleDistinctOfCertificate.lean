import AFTD.Prelude
import AFTD.Kb.Tcs.EightRegularTriangleDistinctCertificate
import AFTD.Kb.Tcs.SimpleGraphRegularOfDegreeIffNeighborCard
import AFTD.Kb.Tcs.SimpleGraphIsTriangleDistinctDecidable
import AFTD.Kb.Tcs.SimpleGraphIsTriangleDistinct
import AFTD.Kb.Tcs.SimpleGraphOfEdgeList
import AFTD.Kb.Tcs.SimpleGraphOfEdgeListDecidableRel

/-!
# eight_regular_triangle_distinct_of_certificate

Topic: graphs   Node: f19918119810

Provenance: helper lemma. step towards regular_eight_triangle_distinct_witness

If the computable certificate checker accepts the edge list L on the n vertices {0,…,n−1}, then the graph of L is 8-regular and has pairwise distinct vertex triangle-degrees. Consequently any accepted list is, on its own, a proof that the existential regularity-8 witness statement holds at that order.
-/

/-- Soundness of the computable certificate checker: a true check yields an 8-regular triangle-distinct graph. -/
theorem eight_regular_triangle_distinct_of_certificate {n : ℕ} (L : List (Fin n × Fin n))
    (h : eight_regular_triangle_distinct_certificate L = true) :
    (simple_graph_of_edge_list L).IsRegularOfDegree 8 ∧
      simple_graph_is_triangle_distinct (simple_graph_of_edge_list L) := by
  rw [eight_regular_triangle_distinct_certificate, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, of_decide_eq_true h2⟩
  rw [simple_graph_regular_of_degree_iff_neighbor_card]
  intro v
  have := (List.all_eq_true.mp h1) v (List.mem_finRange v)
  simpa using this
