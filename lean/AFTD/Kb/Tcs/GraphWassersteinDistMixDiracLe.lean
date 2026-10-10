import AFTD.Prelude
import AFTD.Kb.Tcs.GraphWassersteinDistLeOfPlan
import AFTD.Kb.Tcs.GraphWassersteinDistGeOfForallPlan
import AFTD.Kb.Tcs.GraphWassersteinDist

/-!
# graph_wasserstein_dist_mix_dirac_le

Topic: graphs   Node: e417c252b771

Provenance: helper lemma. Helper for graph_lly_curvature_le_two_div_dist (OP-164, arXiv:2610.10559 (Edge-Connectivity versus Lin--Lu--Yau Curvature)).

Mixing with point masses: W(tμ + (1−t)δ_x, tν + (1−t)δ_y) ≤ t W(μ, ν) + (1−t) d(x, y) for probability measures μ, ν and t ∈ [0, 1].
-/

theorem graph_wasserstein_dist_mix_dirac_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (μ ν : V → ℝ) (hμ : ∀ a, 0 ≤ μ a) (hν : ∀ b, 0 ≤ ν b)
    (hμ1 : ∑ a, μ a = 1) (hν1 : ∑ b, ν b = 1) (x y : V) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    graph_wasserstein_dist G (fun v => t * μ v + (1 - t) * (if v = x then 1 else 0))
      (fun v => t * ν v + (1 - t) * (if v = y then 1 else 0)) ≤
      t * graph_wasserstein_dist G μ ν + (1 - t) * (G.dist x y : ℝ) := by
  have key : ∀ π : V → V → ℝ, (∀ a b, 0 ≤ π a b) → (∀ a, ∑ b, π a b = μ a) →
      (∀ b, ∑ a, π a b = ν b) →
      graph_wasserstein_dist G (fun v => t * μ v + (1 - t) * (if v = x then 1 else 0))
        (fun v => t * ν v + (1 - t) * (if v = y then 1 else 0)) ≤
        t * (∑ a, ∑ b, (G.dist a b : ℝ) * π a b) + (1 - t) * (G.dist x y : ℝ) := by
    intro π h0 h1 h2
    calc _ ≤ ∑ a, ∑ b, (G.dist a b : ℝ) *
          (t * π a b + (1 - t) * (if a = x then (if b = y then 1 else 0) else 0)) := by
          apply graph_wasserstein_dist_le_of_plan
          · intro a b
            have := h0 a b
            have h1t : 0 ≤ 1 - t := by linarith
            split_ifs <;> positivity
          · intro a
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h1 a]
            by_cases ha : a = x <;> simp [ha]
          · intro b
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h2 b]
            by_cases hb : b = y <;> simp [hb]
      _ = _ := by
          simp only [mul_add, Finset.sum_add_distrib]
          congr 1
          · rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun b _ => ?_
            ring
          · simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
              Finset.mem_univ, if_true, Finset.sum_ite_irrel, Finset.sum_const_zero]
            ring
  rcases eq_or_lt_of_le ht0 with rfl | htpos
  · have := key (fun a b => μ a * ν b) (fun a b => mul_nonneg (hμ a) (hν b))
      (fun a => by rw [← Finset.mul_sum, hν1, mul_one])
      (fun b => by rw [← Finset.sum_mul, hμ1, one_mul])
    simpa using this
  · have hlow : (graph_wasserstein_dist G (fun v => t * μ v + (1 - t) * (if v = x then 1 else 0))
        (fun v => t * ν v + (1 - t) * (if v = y then 1 else 0)) - (1 - t) * (G.dist x y : ℝ)) / t
        ≤ graph_wasserstein_dist G μ ν := by
      apply graph_wasserstein_dist_ge_of_forall_plan G μ ν hμ hν hμ1 hν1
      intro π h0 h1 h2
      rw [div_le_iff₀ htpos]
      have := key π h0 h1 h2
      linarith
    rw [div_le_iff₀ htpos] at hlow
    linarith
