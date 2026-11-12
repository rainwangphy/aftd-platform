import AFTD.Prelude

/-!
# op223_matrix_spectrum_abs_le

Topic: graphs   Node: 52a85cce34ab

Provenance: helper lemma. arXiv:2610.17078 Open Problem 6.1; experiments 22883 and 22914

A real matrix whose spectral radius is at most a nonnegative threshold has every real spectral value bounded in absolute value by that threshold.
-/

open Matrix
open scoped ENNReal

theorem op223_matrix_spectrum_abs_le {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hr : spectralRadius ℝ A ≤ ENNReal.ofReal t) :
    ∀ z ∈ spectrum ℝ A, |z| ≤ t := by
  intro z hz
  have hz' : (‖z‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal t := (le_iSup₂ z hz).trans hr
  rw [ENNReal.coe_nnreal_eq, ENNReal.ofReal_le_ofReal_iff ht] at hz'
  simpa [Real.norm_eq_abs] using hz'
