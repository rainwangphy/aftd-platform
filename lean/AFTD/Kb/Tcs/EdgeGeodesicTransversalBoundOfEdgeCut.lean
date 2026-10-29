import AFTD.Prelude
import AFTD.Kb.Tcs.IsMaximalGeodesic
import AFTD.Kb.Tcs.EdgeGeodesicTransversalNumber
import AFTD.Kb.Tcs.IsEdgeGeodesicTransversal

/-!
# edge_geodesic_transversal_bound_of_edge_cut

Topic: graphs   Node: 136ff5b46a59

Provenance: formalization of a published result. Source: arXiv:2610.36821 Lemma 3

Let G be a connected simple graph. Let S be a finite set of edges of G that is an edge cut induced by a vertex subset X (meaning there exists X : Set V such that for all e, e ∈ S ↔ e ∈ G.edgeSet ∧ ∃ u ∈ X, ∃ v ∉ X, e = s(u, v)). If for all vertices u, v and every walk p from u to v in G such that is_maximal_geodesic p, there exists a unique edge e such that e ∈ S ∧ e ∈ p.edges, then the edge geodesic transversal number of G is at most the cardinality of S.
-/

/-- Lemma 3 of arXiv:2610.36821: An edge cut intersecting every maximal geodesic uniquely gives an upper bound on gt_e(G). -/
theorem edge_geodesic_transversal_bound_of_edge_cut {V : Type*} (G : SimpleGraph V) (hG : G.Connected)
    (S : Finset (Sym2 V))
    (hcut : ∃ X : Set V, ∀ e, e ∈ S ↔ e ∈ G.edgeSet ∧ ∃ u ∈ X, ∃ v ∉ X, e = s(u, v))
    (h_inter : ∀ ⦃u v : V⦄ (p : G.Walk u v), is_maximal_geodesic p → ∃! e, e ∈ S ∧ e ∈ p.edges) :
    edge_geodesic_transversal_number G ≤ S.card := by
  have _ := hG
  have hS_trans : is_edge_geodesic_transversal G S := by
    constructor
    · intro e he
      rcases hcut with ⟨X, hX⟩
      exact ((hX e).mp he).1
    · intro u v p hp
      have hp_max : is_maximal_geodesic p := by
        dsimp [is_maximal_geodesic]
        tauto
      rcases h_inter p hp_max with ⟨e, ⟨heS, he_p⟩, _⟩
      exact ⟨e, heS, he_p⟩
  dsimp [edge_geodesic_transversal_number]
  apply Nat.sInf_le
  exact ⟨S, hS_trans, rfl⟩
