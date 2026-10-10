import AFTD.Prelude
import AFTD.Kb.Tcs.GraphWassersteinDist
import AFTD.Kb.Tcs.GraphWassersteinDistLeOfPlan

/-!
# graph_wasserstein_dist_self_eq_zero

Topic: graphs   Node: fb77418ef7f5

Provenance: helper lemma. Sanity check of the definitions of arXiv:2610.10559 (Edge-Connectivity versus Lin--Lu--Yau Curvature), Definition 2.1.

The Wasserstein distance from a nonnegative measure to itself is 0.
-/

theorem graph_wasserstein_dist_self_eq_zero {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (μ : V → ℝ) (hμ : ∀ a, 0 ≤ μ a) :
    graph_wasserstein_dist G μ μ = 0 := by
  let π : V → V → ℝ := fun a b => if a = b then μ a else 0
  have hπ : ∀ a b, 0 ≤ π a b := fun a b => by
    dsimp [π]
    split_ifs
    · exact hμ a
    · rfl
  have h1 : ∀ a, ∑ b, π a b = μ a := fun a => by simp [π]
  have h2 : ∀ b, ∑ a, π a b = μ b := fun b => by simp [π]
  have hcost : ∑ a, ∑ b, (G.dist a b : ℝ) * π a b = 0 := by simp [π]
  have hle : graph_wasserstein_dist G μ μ ≤ 0 := by
    have := graph_wasserstein_dist_le_of_plan G μ μ π hπ h1 h2
    rwa [hcost] at this
  have hge : 0 ≤ graph_wasserstein_dist G μ μ := by
    dsimp [graph_wasserstein_dist]
    apply le_csInf
    · exact ⟨0, π, hπ, h1, h2, hcost.symm⟩
    · rintro c ⟨p, hp, -, -, rfl⟩
      exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => mul_nonneg (by positivity) (hp a b)
  exact le_antisymm hle hge
