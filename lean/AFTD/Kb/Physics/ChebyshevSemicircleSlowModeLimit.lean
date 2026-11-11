import AFTD.Prelude

/-!
# chebyshev_semicircle_slow_mode_limit

Topic: statistical_mechanics   Node: 838267e9ec11

Provenance: formalization of a published result. Source: arXiv:2609.13387

The limiting quantum slow-mode dephasing profile for cycle length m at rescaled time t, defined as the squared modulus of the integral of exp(i * t * U_{m-1}(x/2)) against the Wigner semicircle distribution on [-2, 2].
-/

/-- Chebyshev-semicircle limiting profile for the m-cycle quantum slow mode at rescaled time t. -/
noncomputable def chebyshev_semicircle_slow_mode_limit (m : ℕ) (t : ℝ) : ℝ := ‖∫ x in (-2 : ℝ)..2,
    Complex.exp (Complex.I * (t * (Polynomial.Chebyshev.U ℝ (m - 1)).eval (x / 2) : ℂ)) *
      ((Real.sqrt (4 - x ^ 2) / (2 * Real.pi) : ℝ) : ℂ)‖ ^ 2
