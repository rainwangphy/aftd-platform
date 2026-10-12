import AFTD.Prelude

/-!
# simple_graph_connected_degree_pos

Topic: graphs   Node: 68cf730849bd

Provenance: helper lemma. Helper for arXiv:2610.12109 (Sharp linear Turán remainders for cycle and edge extremality), Lemma 2.5 (equality case of the lower bound: the extremal tree is a path).

In a connected graph with at least two vertices every vertex has positive degree.
-/

theorem simple_graph_connected_degree_pos {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (hk : 2 ≤ Fintype.card V)
    (v : V) : 0 < G.degree v := by
  obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card (by omega) v
  obtain ⟨p⟩ := hconn.preconnected v w
  cases p with
  | nil => exact absurd rfl hw
  | @cons _ x _ h _ =>
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact Finset.card_pos.2 ⟨x, (SimpleGraph.mem_neighborFinset _ _ _).2 h⟩
