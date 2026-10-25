import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphV3

/-!
# maxDegree_induce_V3_le_two_iff

Topic: graphs   Node: 8584410756b0

Provenance: helper lemma. arXiv:2610.21868 Sec. 4

For any finite simple graph G with decidable adjacency on a finite type V with decidable equality, the induced subgraph on the set of degree-3 vertices has maximum degree at most 2 if and only if every vertex in that set has degree at most 2 in the induced subgraph.
-/

/-- Equivalence between maxDegree of G[V_3] <= 2 and every vertex in V_3 having degree <= 2. -/
theorem maxDegree_induce_V3_le_two_iff {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.induce (simple_graph_V3 G : Set V)).maxDegree ≤ 2 ↔
      ∀ v : (simple_graph_V3 G : Set V), (G.induce (simple_graph_V3 G : Set V)).degree v ≤ 2 := by
  constructor
  · intro h v
    exact ((G.induce (simple_graph_V3 G : Set V)).degree_le_maxDegree v).trans h
  · intro h
    exact (G.induce (simple_graph_V3 G : Set V)).maxDegree_le_of_forall_degree_le 2 h
