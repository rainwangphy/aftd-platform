import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleDegree

/-!
# simple_graph_triangle_degree_le_choose

Topic: graphs   Node: 50e050826d41

Provenance: helper lemma. Sanity lemma for simple_graph_triangle_degree (arXiv:2610.08478 (Regular K_3-Irregular Graphs of Every Regularity at Least Nine)); used for the order bound on regular triangle-distinct graphs.

td_G(v) ≤ C(deg v, 2).
-/

theorem simple_graph_triangle_degree_le_choose {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    simple_graph_triangle_degree G v ≤ (G.degree v).choose 2 := by
  unfold simple_graph_triangle_degree
  calc _ ≤ ((G.neighborFinset v).powersetCard 2).card := Finset.card_filter_le _ _
    _ = (G.degree v).choose 2 := by rw [Finset.card_powersetCard, SimpleGraph.card_neighborFinset_eq_degree]
