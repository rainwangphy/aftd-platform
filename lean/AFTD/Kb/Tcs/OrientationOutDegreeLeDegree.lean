import AFTD.Prelude
import AFTD.Kb.Tcs.IsGraphOrientation

/-!
# orientation_out_degree_le_degree

Topic: graphs   Node: 27aeefb2bb7e

Provenance: helper lemma. arXiv:2610.30174, Theorem 2.1

In any orientation D of a finite simple graph G, the out-degree of any vertex v in D is at most the degree of v in G.
-/

/-- In any orientation of a graph G, the out-degree of each vertex is at most its degree in G. -/
lemma orientation_out_degree_le_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Digraph V) [DecidableRel D.Adj]
    (hD : is_graph_orientation G D) (v : V) :
    (Finset.filter (D.Adj v) Finset.univ).card ≤ G.degree v := by
  rw [SimpleGraph.degree]
  apply Finset.card_le_card
  intro u hu
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rw [SimpleGraph.mem_neighborFinset]
  exact (hD.1 v u).mp (Or.inl hu)
