import AFTD.Prelude
import AFTD.Kb.Tcs.GraphWassersteinDist

/-!
# graph_wasserstein_dist_le_of_plan

Topic: graphs   Node: 60e530159bd8

Provenance: helper lemma. Helper for the curvature computations of arXiv:2610.10559 (Edge-Connectivity versus Lin--Lu--Yau Curvature) (upper bounds on W by explicit plans, as in the proof of Lemma 3.2).

The Wasserstein distance is at most the cost of any transport plan.
-/

theorem graph_wasserstein_dist_le_of_plan {V : Type*} [Fintype V] (G : SimpleGraph V)
    (μ ν : V → ℝ) (π : V → V → ℝ) (hπ : ∀ a b, 0 ≤ π a b) (h1 : ∀ a, ∑ b, π a b = μ a)
    (h2 : ∀ b, ∑ a, π a b = ν b) :
    graph_wasserstein_dist G μ ν ≤ ∑ a, ∑ b, (G.dist a b : ℝ) * π a b := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro c ⟨p, hp, -, -, rfl⟩
    exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => mul_nonneg (by positivity) (hp a b)
  · exact ⟨π, hπ, h1, h2, rfl⟩
