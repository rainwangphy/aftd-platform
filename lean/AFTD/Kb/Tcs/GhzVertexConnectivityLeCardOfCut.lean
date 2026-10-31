import AFTD.Prelude
import AFTD.Kb.Tcs.GhzGraphVertexConnectivity

/-!
# ghz_vertex_connectivity_le_card_of_cut

Topic: graphs   Node: 0acc9c8bac2b

Provenance: helper lemma. step towards radius_independence_connectivity_hamiltonian_radius_two

If a finite vertex set T has G − T not preconnected, then the vertex connectivity κ(G) is at most |T|.
-/

/-- Cut bound: a witness cut set of size |T| upper-bounds κ(G); used to get κ(G) ≤ |A|. -/
theorem ghz_vertex_connectivity_le_card_of_cut {V : Type*} [Fintype V] (G : SimpleGraph V)
    (T : Finset V) (h : ¬ (SimpleGraph.induce ((T : Set V))ᶜ G).Preconnected) :
    ghz_graph_vertex_connectivity G ≤ T.card := by
  classical
  unfold ghz_graph_vertex_connectivity
  split_ifs with hG
  · exfalso
    apply h
    rw [hG, SimpleGraph.induce_top]
    intro u v
    exact SimpleGraph.reachable_top
  · exact Nat.sInf_le ⟨T, h, rfl⟩
