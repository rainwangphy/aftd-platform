import AFTD.Prelude

/-!
# spectral_min_re

Topic: quantum   Node: c5400a40c964

Provenance: formalization of a published result. Source: arXiv:2610.37187 Sec. 2

The minimal real part m(Φ) of an eigenvalue of a linear map Φ on d × d complex matrices is the infimum of the real parts of the elements in the complex spectrum of Φ.
-/

/-- The minimum real part of an eigenvalue in the spectrum of a linear operator Φ on d × d complex matrices. -/
noncomputable def spectral_min_re (d : ℕ) (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) : ℝ := sInf (Complex.re '' spectrum ℂ Φ)
