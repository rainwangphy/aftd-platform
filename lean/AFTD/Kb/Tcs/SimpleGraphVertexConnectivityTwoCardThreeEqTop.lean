import AFTD.Prelude
import AFTD.Kb.Tcs.GhzGraphVertexConnectivityLeCardSubTwo
import AFTD.Kb.Tcs.GhzGraphVertexConnectivity

/-!
# simple_graph_vertex_connectivity_two_card_three_eq_top

Topic: graphs   Node: a953b9cb3c0b

Provenance: helper lemma. step towards radius_independence_connectivity_hamiltonian_interpolation

If a graph G on 3 vertices had G ≠ ⊤, then by ghz_graph_vertex_connectivity_le_card_sub_two its vertex connectivity would be at most 3 - 2 = 1, contradicting κ(G) ≥ 2. Hence G = ⊤.
-/

/-- Any 2-connected simple graph on 3 vertices is the complete graph K_3. -/
theorem simple_graph_vertex_connectivity_two_card_three_eq_top {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hcard : Fintype.card V = 3) (hκ : 2 ≤ ghz_graph_vertex_connectivity G) : G = ⊤ := by
  by_contra hne
  have h := ghz_graph_vertex_connectivity_le_card_sub_two G hne
  omega
