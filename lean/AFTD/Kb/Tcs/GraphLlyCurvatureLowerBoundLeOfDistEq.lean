import AFTD.Prelude
import AFTD.Kb.Tcs.GraphLlyCurvatureLowerBound
import AFTD.Kb.Tcs.GraphLlyCurvature

/-!
# graph_lly_curvature_lower_bound_le_of_dist_eq

Topic: graphs   Node: 70fc67888768

Provenance: helper lemma. step towards exists_dist_three_lly_curvature_le_cut

The scale-i lower curvature bound is a lower bound for κ_LLY at any pair at distance i: κ_LLY^(i)(G) ≤ κ_LLY(x,y) whenever d(x,y) = i.
-/

/-- The infimum defining κ_LLY^(i)(G) is attained-below by every distance-i pair. -/
theorem graph_lly_curvature_lower_bound_le_of_dist_eq
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y : V) (i : ℕ) (h : G.dist x y = i) :
    graph_lly_curvature_lower_bound G i ≤ graph_lly_curvature G x y := by
  unfold graph_lly_curvature_lower_bound
  have hS : ({κ : ℝ | ∃ x y, G.dist x y = i ∧ graph_lly_curvature G x y = κ}
      ⊆ Set.range (fun p : V × V => graph_lly_curvature G p.1 p.2)) := by
    rintro κ ⟨a, b, -, rfl⟩
    exact ⟨(a, b), rfl⟩
  have hfin : ({κ : ℝ | ∃ x y, G.dist x y = i ∧ graph_lly_curvature G x y = κ}).Finite :=
    Set.Finite.subset (Set.finite_range _) hS
  exact csInf_le hfin.bddBelow ⟨x, y, h, rfl⟩
