import AFTD.Prelude
import AFTD.Kb.Tcs.EdgeMaxCliqueOrder

/-!
# edge_max_clique_order_le_card

Topic: graphs   Node: 02d34ba6558d

Provenance: helper lemma. scout/2611-30029-an-exact-vertex-localization-of-zykov-s-theorem.md:211

For every edge e ∈ G.edgeSet of a finite simple graph G on vertex type V, the maximum order of a clique containing e is at most the cardinality of V (Fintype.card V).
-/

/-- The maximum order of a clique containing an edge is at most the number of vertices. -/
theorem edge_max_clique_order_le_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (e : Sym2 V) (he : e ∈ G.edgeSet) :
    edge_max_clique_order G e ≤ Fintype.card V := by
  have _ := he
  unfold edge_max_clique_order
  apply Finset.sup_le
  intro s _
  exact s.card_le_univ
