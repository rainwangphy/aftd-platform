import AFTD.Prelude
import AFTD.Kb.Tcs.EuclideanHasMonoAp
import AFTD.Kb.Tcs.Mod5RationalQuadraticBlueWitness
import AFTD.Kb.Tcs.NormSqApQuadratic

/-!
# spherical_mod5_scale149_100_blue_unit_ap

Topic: combinatorics   Node: 6e43b86720d1

Provenance: helper lemma. Exact rational witness from experiment 25409 for OP-1482.

The planar radial coloring that colors x true exactly when floor((149/100)‖x‖²) is nonzero modulo 5 has a true 17-term arithmetic progression with unit spacing.
-/

theorem spherical_mod5_scale149_100_blue_unit_ap : euclidean_has_mono_ap (fun x : EuclideanSpace ℝ (Fin 2) => decide ((⌊(149 / 100 : ℝ) * ‖x‖^2⌋ : ℤ) % 5 ≠ 0)) 17 1 true := by
  let x : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![(183 / 149 : ℝ), 1]
  let v : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![(1 : ℝ), 0]
  refine ⟨x, v, ?_, ?_⟩
  · have hv : ‖v‖^2 = 1 := by
      simp [v, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    have hn := norm_nonneg v
    nlinarith
  · intro k
    simp only [decide_eq_true_eq]
    have hv : (149 / 100 : ℝ) * ‖x + (k : ℝ) • v‖^2 =
        (149 / 100 : ℝ) * (k.val : ℝ)^2 + (183 / 50 : ℝ) * k.val + 5569 / 1490 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [x, v, Fin.sum_univ_two] <;> ring
    rw [hv]
    exact mod5_rational_quadratic_blue_witness k
