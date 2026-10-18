import AFTD.Prelude
import AFTD.Kb.Tcs.GraphLlyCurvatureLeTwoDivDist
import AFTD.Kb.Tcs.GraphLlyCurvatureLowerBound
import AFTD.Kb.Tcs.GraphLlyCurvature

/-!
# graph_lly_curvature_lower_bound_two_le_one

Topic: graphs   Node: 0c6f2113af13

Provenance: helper lemma. step towards edge_connectivity_ge_min_degree_mul_lly_lower_bound_two

For every finite connected graph G, the lower Lin–Lu–Yau curvature bound at scale 2 is at most 1: κ_LLY^(2)(G) ≤ 2/2 = 1.
-/

/-- The scale-2 curvature bound is at most 1, since κ_LLY(x,y) ≤ 2/d(x,y) = 1 for d(x,y)=2. -/
theorem graph_lly_curvature_lower_bound_two_le_one {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) :
    graph_lly_curvature_lower_bound G 2 ≤ 1 := by
  unfold graph_lly_curvature_lower_bound
  rcases Set.eq_empty_or_nonempty {κ | ∃ x y : V, G.dist x y = 2 ∧ graph_lly_curvature G x y = κ} with he | hne_set
  · rw [he, Real.sInf_empty]
    norm_num
  · rcases hne_set with ⟨_, x, y, hxy, rfl⟩
    have hfin : ({κ | ∃ x y : V, G.dist x y = 2 ∧ graph_lly_curvature G x y = κ} : Set ℝ).Finite := by
      have : {κ | ∃ x y : V, G.dist x y = 2 ∧ graph_lly_curvature G x y = κ} ⊆
          Set.range (fun p : V × V => graph_lly_curvature G p.1 p.2) := by
        rintro _ ⟨a, b, -, rfl⟩
        exact ⟨(a, b), rfl⟩
      exact (Set.finite_range _).subset this
    have hle := csInf_le hfin.bddBelow ⟨x, y, hxy, rfl⟩
    have hne : x ≠ y := by
      rintro rfl
      simp at hxy
    have hcurv := graph_lly_curvature_le_two_div_dist G hG x y hne
    rw [hxy] at hcurv
    norm_num at hcurv
    exact le_trans hle hcurv
