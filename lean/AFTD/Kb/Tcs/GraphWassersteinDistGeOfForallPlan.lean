import AFTD.Prelude
import AFTD.Kb.Tcs.GraphWassersteinDist

/-!
# graph_wasserstein_dist_ge_of_forall_plan

Topic: graphs   Node: 42627bd91249

Provenance: helper lemma. Helper for graph_lly_curvature_le_two_div_dist (OP-164, arXiv:2610.10559 (Edge-Connectivity versus Lin--Lu--Yau Curvature)).

A lower bound on the cost of every transport plan between two probability measures is a lower bound on their Wasserstein distance.
-/

theorem graph_wasserstein_dist_ge_of_forall_plan {V : Type*} [Fintype V] (G : SimpleGraph V)
    (μ ν : V → ℝ) (hμ : ∀ a, 0 ≤ μ a) (hν : ∀ b, 0 ≤ ν b) (hμ1 : ∑ a, μ a = 1)
    (hν1 : ∑ b, ν b = 1) (c : ℝ)
    (h : ∀ π : V → V → ℝ, (∀ a b, 0 ≤ π a b) → (∀ a, ∑ b, π a b = μ a) →
      (∀ b, ∑ a, π a b = ν b) → c ≤ ∑ a, ∑ b, (G.dist a b : ℝ) * π a b) :
    c ≤ graph_wasserstein_dist G μ ν := by
  unfold graph_wasserstein_dist
  apply le_csInf
  · refine ⟨_, fun a b => μ a * ν b, fun a b => mul_nonneg (hμ a) (hν b), ?_, ?_, rfl⟩
    · intro a; rw [← Finset.mul_sum, hν1, mul_one]
    · intro b; rw [← Finset.sum_mul, hμ1, one_mul]
  · rintro c' ⟨π, h0, h1, h2, rfl⟩
    exact h π h0 h1 h2
