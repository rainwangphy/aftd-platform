import AFTD.Prelude
import AFTD.Kb.Tcs.GraphStackingNumber
import AFTD.Kb.Tcs.SimpleGraphTreeEstimate
import AFTD.Kb.Tcs.GraphConfigStackable
import AFTD.Kb.Tcs.GraphPebblingStep

/-!
# star_graph_one_stacking_number_eq_tree_estimate

Topic: graphs   Node: 68b294eb1ed2

Provenance: formalization of a published result. Source: arXiv:2610.09650 Thm 5.2

Conjecture 5.6 (OP-144) holds for the single-vertex tree K₁: stack(K₁) = estim(K₁) (both equal 2).
-/

theorem star_graph_one_stacking_number_eq_tree_estimate_stacking_number :
    graph_stacking_number (SimpleGraph.starGraph (0 : Fin 1)) = 2 := by
  unfold graph_stacking_number
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨le_rfl, ?_⟩
    intro c hc
    unfold graph_config_stackable
    refine ⟨c, Relation.ReflTransGen.refl, 0, ?_, ?_⟩
    · have h_sum : ∑ v : Fin 1, c v = c 0 := by
        have : (Finset.univ : Finset (Fin 1)) = {0} := rfl
        rw [← Finset.sum_singleton c 0, ← this]
      rw [h_sum] at hc
      omega
    · intro w hw
      have : w = 0 := Subsingleton.elim w 0
      exact False.elim (hw this)
  · intro t ht
    exact ht.1

theorem star_graph_one_stacking_number_eq_tree_estimate_tree_estimate :
    simple_graph_tree_estimate (SimpleGraph.starGraph (0 : Fin 1)) = 2 := by
  unfold simple_graph_tree_estimate
  have h_univ : (Finset.univ : Finset (Fin 1)) = {0} := rfl
  rw [h_univ]
  simp only [Finset.sup_singleton]
  have h_leaf : {v ∈ ({0} : Finset (Fin 1)) | v ≠ (0 : Fin 1) ∧ (SimpleGraph.starGraph (0 : Fin 1)).degree v = 1} = ∅ := by
    decide
  rw [h_leaf]
  simp only [Finset.card_empty, add_zero]
  have h_sum : (∑ v ∈ {0} with v = (0 : Fin 1) ∨ 1 < (SimpleGraph.starGraph (0 : Fin 1)).degree v,
      (SimpleGraph.starGraph (0 : Fin 1)).degree v * 2 ^ (SimpleGraph.starGraph (0 : Fin 1)).dist 0 v) = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    have hv : (SimpleGraph.starGraph (0 : Fin 1)).degree v = 0 := by
      have : v = 0 := Subsingleton.elim v 0
      subst this
      decide
    rw [hv, zero_mul]
  rw [h_sum]
  rfl

/-- OP-144 holds for the single-vertex tree K₁: stack(K₁) = estim(K₁) = 2. -/
theorem star_graph_one_stacking_number_eq_tree_estimate :
    graph_stacking_number (SimpleGraph.starGraph (0 : Fin 1)) =
      simple_graph_tree_estimate (SimpleGraph.starGraph (0 : Fin 1)) := by
  rw [star_graph_one_stacking_number_eq_tree_estimate_stacking_number,
      star_graph_one_stacking_number_eq_tree_estimate_tree_estimate]
