import AFTD.Prelude

/-!
# graph_degree_pos_of_connected_of_ne

Topic: graphs   Node: 472073eaf996

Provenance: helper lemma. Helper for graph_lly_curvature_le_two_div_dist (OP-164, arXiv:2610.10559 (Edge-Connectivity versus Lin--Lu--Yau Curvature)).

In a connected graph, a vertex x with some other vertex y has positive degree.
-/

theorem graph_degree_pos_of_connected_of_ne {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (x y : V) (hxy : x ≠ y) :
    0 < G.degree x := by
  obtain ⟨p⟩ := hG.preconnected x y
  cases p with
  | nil => exact absurd rfl hxy
  | cons h _ => exact (G.degree_pos_iff_exists_adj x).mpr ⟨_, h⟩
