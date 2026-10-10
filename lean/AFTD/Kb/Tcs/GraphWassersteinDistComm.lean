import AFTD.Prelude
import AFTD.Kb.Tcs.GraphWassersteinDist

/-!
# graph_wasserstein_dist_comm

Topic: graphs   Node: d465c7217081

Provenance: helper lemma. Helper for the refutation of OP-165 (arXiv:2610.10559, after Theorem 1.4).

The Wasserstein distance is symmetric: W(μ, ν) = W(ν, μ).
-/

theorem graph_wasserstein_dist_comm {V : Type*} [Fintype V] (G : SimpleGraph V)
    (μ ν : V → ℝ) : graph_wasserstein_dist G μ ν = graph_wasserstein_dist G ν μ := by
  unfold graph_wasserstein_dist
  congr 1
  ext c
  constructor
  · rintro ⟨π, h0, h1, h2, rfl⟩
    refine ⟨fun a b => π b a, fun a b => h0 b a, h2, h1, ?_⟩
    rw [Finset.sum_comm]
    simp_rw [SimpleGraph.dist_comm]
  · rintro ⟨π, h0, h1, h2, rfl⟩
    refine ⟨fun a b => π b a, fun a b => h0 b a, h2, h1, ?_⟩
    rw [Finset.sum_comm]
    simp_rw [SimpleGraph.dist_comm]
