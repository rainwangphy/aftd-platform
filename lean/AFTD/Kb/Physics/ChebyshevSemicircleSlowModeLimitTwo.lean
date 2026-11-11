import AFTD.Prelude
import AFTD.Kb.Physics.ChebyshevSemicircleSlowModeLimit

/-!
# chebyshev_semicircle_slow_mode_limit_two

Topic: statistical_mechanics   Node: 7260c92be2db

Provenance: helper lemma. arXiv:2609.13387

For random transpositions (cycle length m = 2), the Chebyshev polynomial U_1(x/2) simplifies to x, so the slow-mode limiting profile is the squared modulus of the Fourier transform of the Wigner semicircle distribution on [-2, 2].
-/

/-- For m = 2, the Chebyshev-semicircle limit reduces to the squared modulus of the semicircle Fourier transform. -/
theorem chebyshev_semicircle_slow_mode_limit_two (t : ℝ) :
    chebyshev_semicircle_slow_mode_limit 2 t =
      ‖∫ x in (-2 : ℝ)..2,
        Complex.exp (Complex.I * (t * (x : ℂ))) *
          ((Real.sqrt (4 - x ^ 2) / (2 * Real.pi) : ℝ) : ℂ)‖ ^ 2 := by
  unfold chebyshev_semicircle_slow_mode_limit
  congr 2
  apply intervalIntegral.integral_congr
  intro x _
  dsimp
  rw [Polynomial.Chebyshev.U_one]
  have h : Polynomial.eval (x / 2) (2 * Polynomial.X : Polynomial ℝ) = x := by
    simp; ring
  rw [h]
