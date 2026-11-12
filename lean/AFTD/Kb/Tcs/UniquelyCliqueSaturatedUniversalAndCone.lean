import AFTD.Prelude
import AFTD.Kb.Tcs.IsUniquelyCliqueSaturated
import AFTD.Kb.Tcs.SimpleGraphCone
import AFTD.Kb.Tcs.UniquelyCliqueSaturatedVertexDeletedOfUniversal
import AFTD.Kb.Tcs.UniquelyCliqueSaturatedCone

/-!
# uniquely_clique_saturated_universal_and_cone

Topic: graphs   Node: f32417f37480

Provenance: formalization of a published result. Source: arXiv:2611.13656 Proposition 2.1

Let r ≥ 3 be an integer, and let G be a finite simple graph. If G is uniquely K_r-saturated, then (i) for every universal vertex x of G, the vertex-deleted subgraph G - x is uniquely K_{r-1}-saturated, and (ii) the cone G ∨ K_1 is uniquely K_{r+1}-saturated.
-/

/-- Universal vertices and cone extensions in uniquely clique-saturated graphs (Proposition 2.1). -/
theorem uniquely_clique_saturated_universal_and_cone
    {V : Type*} [Fintype V] (G : SimpleGraph V) {r : ℕ} (hr : 3 ≤ r)
    (hG : is_uniquely_clique_saturated G r) :
    (∀ x : V, G.IsUniversal x → is_uniquely_clique_saturated (G.induce (Set.univ \ {x})) (r - 1)) ∧
    is_uniquely_clique_saturated (simple_graph_cone G) (r + 1) := by
  exact ⟨fun x hx => uniquely_clique_saturated_vertex_deleted_of_universal G hr hG x hx,
    uniquely_clique_saturated_cone G hr hG⟩
