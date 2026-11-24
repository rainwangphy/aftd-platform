import AFTD.Prelude
import AFTD.Kb.Tcs.IsKFactorCritical
import AFTD.Kb.Tcs.FactorcriticalOddGroupsDeletedVertexBound

/-!
# factorcritical_odd_groups_outside_vertex_bound

Topic: graphs   Node: 539832523288

Provenance: helper lemma. OP-1957: stronger factor-critical block count for arbitrary barrier components.

In a factor-critical graph, pairwise disjoint odd sets anticomplete to the rest of L require at least one distinct matching partner outside L for each set, after deleting any specified vertex outside L; consequently the outside of L has at least one more vertex than the number of odd sets.
-/

theorem factorcritical_odd_groups_outside_vertex_bound
    {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hcrit : is_k_factor_critical H 1)
    (J : Finset I) (F : I → Finset V) (L : Finset V)
    (hsub : ∀ i ∈ J, F i ⊆ L)
    (hodd : ∀ i ∈ J, Odd (F i).card)
    (hdis : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (F i) (F j))
    (hanti : ∀ i ∈ J, ∀ u ∈ F i, ∀ v ∈ L, v ∉ F i → ¬ H.Adj u v)
    (z : V) (hzL : z ∉ L) :
    J.card + 1 ≤ ((Finset.univ : Finset V) \ L).card := by
  classical
  have hz : ∀ i ∈ J, z ∉ F i := fun i hi hzi => hzL (hsub i hi hzi)
  have hb := factorcritical_odd_groups_deleted_vertex_bound H hcrit J F L hsub hodd hdis hanti z hz
  have hmem : z ∈ ((Finset.univ : Finset V) \ L) := by simp [hzL]
  rw [Finset.card_erase_of_mem hmem] at hb
  have hc := Finset.card_pos.mpr ⟨z,hmem⟩
  omega
