import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphVertexConnectivityTwoCardThreeEqTop
import AFTD.Kb.Tcs.SimpleGraphTopIsHamiltonian
import AFTD.Kb.Tcs.GhzGraphVertexConnectivity

/-!
# simple_graph_vertex_connectivity_two_card_three_hamiltonian

Topic: graphs   Node: a55b6c59970e

Provenance: helper lemma. step towards radius_independence_connectivity_hamiltonian_interpolation

For card V = 3 and κ(G) ≥ 2, simple_graph_vertex_connectivity_two_card_three_eq_top forces G = ⊤. Then simple_graph_top_is_hamiltonian yields G.IsHamiltonian.
-/

/-- Every 2-connected simple graph on 3 vertices contains a Hamilton cycle. -/
theorem simple_graph_vertex_connectivity_two_card_three_hamiltonian {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hcard : Fintype.card V = 3) (hκ : 2 ≤ ghz_graph_vertex_connectivity G) : G.IsHamiltonian := by
  have h : G = ⊤ := simple_graph_vertex_connectivity_two_card_three_eq_top G hcard hκ
  rw [h]
  exact simple_graph_top_is_hamiltonian (by omega : 3 ≤ Fintype.card V)
