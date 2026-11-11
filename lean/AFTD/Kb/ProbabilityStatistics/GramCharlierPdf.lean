import AFTD.Prelude

/-!
# gram_charlier_pdf

Topic: minimax   Node: 6bd074cfee61

Provenance: formalization of a published result. Source: arXiv:2611.11852: Section 2.1

The fourth-order Gram-Charlier probability density function with excess kurtosis parameter a is phi_a(s) = phi(s) * (1 + a * (s^4 - 6 * s^2 + 3) / 24), where phi is the standard normal density.
-/

/-- The Gram-Charlier probability density function with excess kurtosis parameter a. -/
noncomputable def gram_charlier_pdf (a : ℝ) (s : ℝ) : ℝ := (1 / Real.sqrt (2 * Real.pi)) * Real.exp (- s ^ 2 / 2) * (1 + a * (s ^ 4 - 6 * s ^ 2 + 3) / 24)
