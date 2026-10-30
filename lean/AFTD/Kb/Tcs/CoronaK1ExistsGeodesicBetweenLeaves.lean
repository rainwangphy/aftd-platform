import AFTD.Prelude
import AFTD.Kb.Tcs.CoronaK1
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# corona_k1_exists_geodesic_between_leaves

Topic: graphs   Node: ddeefa84886f

Provenance: helper lemma. step towards edge_geodesic_transversal_number_corona_k1

For every finite type V and every connected simple graph G on V, between any two leaves Sum.inr u and Sum.inr v in corona_k1 G, there exists a walk that is a path and has length equal to the distance between them.
-/

/-- Between any two leaves in the corona product corona_k1 G of a connected graph, there exists a path that is a geodesic. -/
theorem corona_k1_exists_geodesic_between_leaves
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.Connected) (u v : V) :
    ∃ p : (corona_k1 G).Walk (Sum.inr u) (Sum.inr v),
      p.IsPath ∧ p.length = (corona_k1 G).dist (Sum.inr u) (Sum.inr v) := by
  have h_reach_G : G.Reachable u v := hG u v
  have h1 : (corona_k1 G).Adj (Sum.inr u) (Sum.inl u) := rfl
  have h2 : (corona_k1 G).Reachable (Sum.inl u) (Sum.inl v) :=
    SimpleGraph.Reachable.map ⟨Sum.inl, fun h => h⟩ h_reach_G
  have h3 : (corona_k1 G).Adj (Sum.inl v) (Sum.inr v) := rfl
  have h_reach : (corona_k1 G).Reachable (Sum.inr u) (Sum.inr v) :=
    (h1.reachable.trans h2).trans h3.reachable
  exact h_reach.exists_path_of_dist
