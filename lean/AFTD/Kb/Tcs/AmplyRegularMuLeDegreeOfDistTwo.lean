import AFTD.Prelude
import AFTD.Kb.Tcs.IsAmplyRegular

/-!
# amply_regular_mu_le_degree_of_dist_two

Topic: graphs   Node: 88a7d910e034

Provenance: helper lemma. step towards simple_graph_diam_le_two_mul_div_add_one_of_dist_two_transport_bound

In an amply regular graph with parameters (k, ℓ, μ), if there exists a pair of vertices at distance 2, then μ ≤ k.
-/

/-- In an amply regular graph with parameters (k, ℓ, μ), if there exists a pair of vertices at distance 2, then μ ≤ k. -/
theorem amply_regular_mu_le_degree_of_dist_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {k ℓ μ : ℕ} (hG : IsAmplyRegular G k ℓ μ)
    {u v : V} (huv : G.dist u v = 2) : μ ≤ k := by
  have hsub : G.commonNeighbors u v ⊆ G.neighborSet u := by
    intro w hw
    rw [SimpleGraph.mem_commonNeighbors] at hw
    exact hw.1
  have hcard : Fintype.card (G.commonNeighbors u v) ≤ Fintype.card (G.neighborSet u) := by
    refine Fintype.card_le_of_injective (fun w : G.commonNeighbors u v => (⟨w.1, hsub w.2⟩ : G.neighborSet u)) ?_
    intro a b h
    ext
    exact congrArg (fun x : G.neighborSet u => (x : V)) h
  rw [← hG.dist_two_commonNeighbors huv]
  calc
    Fintype.card (G.commonNeighbors u v) ≤ Fintype.card (G.neighborSet u) := hcard
    _ = G.degree u := SimpleGraph.card_neighborSet_eq_degree G u
    _ = k := hG.regular.degree_eq u
