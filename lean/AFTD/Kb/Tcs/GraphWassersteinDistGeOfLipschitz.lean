import AFTD.Prelude
import AFTD.Kb.Tcs.GraphWassersteinDist

/-!
# graph_wasserstein_dist_ge_of_lipschitz

Topic: graphs   Node: 8a0817d6873f

Provenance: helper lemma. Helper for the curvature computations of arXiv:2610.10559 (Edge-Connectivity versus Lin--Lu--Yau Curvature); the easy half of the Kantorovich duality quoted in Sec. 2.2.

Weak Kantorovich duality: for probability measures μ, ν and any function f with f(a) − f(b) ≤ d(a, b), Σ f μ − Σ f ν ≤ W(μ, ν).
-/

theorem graph_wasserstein_dist_ge_of_lipschitz {V : Type*} [Fintype V] (G : SimpleGraph V)
    (μ ν : V → ℝ) (hμ : ∀ a, 0 ≤ μ a) (hν : ∀ b, 0 ≤ ν b) (hμ1 : ∑ a, μ a = 1)
    (hν1 : ∑ b, ν b = 1) (f : V → ℝ) (hf : ∀ a b, f a - f b ≤ (G.dist a b : ℝ)) :
    ∑ a, f a * μ a - ∑ b, f b * ν b ≤ graph_wasserstein_dist G μ ν := by
  apply le_csInf
  · refine ⟨_, fun a b => μ a * ν b, fun a b => mul_nonneg (hμ a) (hν b), ?_, ?_, rfl⟩
    · intro a; rw [← Finset.mul_sum, hν1, mul_one]
    · intro b; rw [← Finset.sum_mul, hμ1, one_mul]
  · rintro c ⟨π, h0, h1, h2, rfl⟩
    have e1 : ∑ a, f a * μ a = ∑ a, ∑ b, f a * π a b := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← h1 a, Finset.mul_sum]
    have e2 : ∑ b, f b * ν b = ∑ a, ∑ b, f b * π a b := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← h2 b, Finset.mul_sum]
    rw [e1, e2, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [← sub_mul]
    exact mul_le_mul_of_nonneg_right (hf a b) (h0 a b)
