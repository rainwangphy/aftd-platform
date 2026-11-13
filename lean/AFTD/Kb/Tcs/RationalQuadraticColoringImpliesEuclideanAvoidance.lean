import AFTD.Prelude
import AFTD.Kb.Tcs.EuclideanAvoidsAp
import AFTD.Kb.Tcs.EuclideanHasMonoAp
import AFTD.Kb.Tcs.NormSqApQuadratic

/-!
# rational_quadratic_coloring_implies_euclidean_avoidance

Topic: combinatorics   Node: 45d3bc61cb86

Provenance: helper lemma. Squared-norm identity from arXiv:2611.12360 Lemma 2.1, plus a rational-linear retraction of the real numbers.

A rational coloring avoiding false length-3 and true length-17 monic quadratic sequences with arbitrary rational lower coefficients yields the required Euclidean coloring in every finite dimension.
-/

theorem rational_quadratic_coloring_implies_euclidean_avoidance (f : ℚ → Bool) (h3 : ∀ a b : ℚ, ¬ ∀ k : Fin 3, f ((k.val : ℚ) ^ 2 + a * k.val + b) = false) (h17 : ∀ a b : ℚ, ¬ ∀ k : Fin 17, f ((k.val : ℚ) ^ 2 + a * k.val + b) = true) : ∀ n : ℕ, euclidean_avoids_ap n 3 1 17 1 := by
  classical
  obtain ⟨L, hL⟩ := Module.Projective.exists_dual_eq_one ℚ (show (1 : ℝ) ≠ 0 by norm_num)
  have hL_rat (r : ℚ) : L (r : ℝ) = r := by
    have h := L.map_smul r (1 : ℝ)
    simpa [hL, Rat.smul_def] using h
  intro n
  let c : EuclideanSpace ℝ (Fin n) → Bool := fun x => f (L (‖x‖^2))
  have hquad (x v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1) (k : ℕ) :
      L (‖x + (k : ℝ) • v‖^2) = (k : ℚ)^2 + L (2 * @inner ℝ _ _ x v) * k + L (‖x‖^2) := by
    rw [norm_sq_ap_quadratic, hv]
    have hid : (1 : ℝ)^2 * (k : ℝ)^2 + 2 * @inner ℝ _ _ x v * (k : ℝ) + ‖x‖^2 =
        (((k : ℚ)^2 : ℚ) : ℝ) + (k : ℚ) • (2 * @inner ℝ _ _ x v) + ‖x‖^2 := by
      simp only [one_pow, one_mul, Rat.cast_pow, Rat.cast_natCast, Rat.smul_def]
      ring
    rw [hid, map_add, map_add, hL_rat, map_smul]
    simp only [smul_eq_mul]
    ring
  refine ⟨c, ?_, ?_⟩
  · rintro ⟨x, v, hv, hc⟩
    apply h3 (L (2 * @inner ℝ _ _ x v)) (L (‖x‖^2))
    intro k
    have hh := hc k
    change f (L (‖x + (k.val : ℝ) • v‖^2)) = false at hh
    rw [hquad x v hv k.val] at hh
    exact hh
  · rintro ⟨x, v, hv, hc⟩
    apply h17 (L (2 * @inner ℝ _ _ x v)) (L (‖x‖^2))
    intro k
    have hh := hc k
    change f (L (‖x + (k.val : ℝ) • v‖^2)) = true at hh
    rw [hquad x v hv k.val] at hh
    exact hh
