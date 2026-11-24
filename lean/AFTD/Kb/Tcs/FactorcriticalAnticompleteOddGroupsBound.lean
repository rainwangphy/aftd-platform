import AFTD.Prelude
import AFTD.Kb.Tcs.IsKFactorCritical
import AFTD.Kb.Tcs.FactorcriticalAnticompleteOddComponentsBound
import AFTD.Kb.Tcs.FactorcriticalOddGroupsDeletedVertexBound

/-!
# factorcritical_anticomplete_odd_groups_bound

Topic: graphs   Node: 252c4d179ffb

Provenance: helper lemma. OP-1957: factor-critical component-count inequality for grouped barrier pieces.

In a finite 1-factor-critical graph, pairwise disjoint odd vertex groups that are each anticomplete to the rest of a set L cannot outnumber the vertices outside L, provided L contains a vertex outside all groups. The groups need not be connected.
-/

theorem factorcritical_anticomplete_odd_groups_bound
    {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hcrit : is_k_factor_critical H 1)
    (J : Finset I) (F : I → Finset V) (L : Finset V)
    (hsub : ∀ i ∈ J, F i ⊆ L)
    (hodd : ∀ i ∈ J, Odd (F i).card)
    (hdis : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (F i) (F j))
    (hanti : ∀ i ∈ J, ∀ u ∈ F i, ∀ v ∈ L, v ∉ F i → ¬ H.Adj u v)
    (z : V) (hzL : z ∈ L) (hz : ∀ i ∈ J, z ∉ F i) :
    J.card ≤ ((Finset.univ : Finset V) \ L).card := by
  classical
  have hb := factorcritical_odd_groups_deleted_vertex_bound H hcrit J F L hsub hodd hdis hanti z hz
  exact le_trans hb (Finset.card_le_card (Finset.erase_subset _ _))
