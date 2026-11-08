import AFTD.Prelude

/-!
# spectral_max_re

Topic: quantum   Node: 1748c33a4f12

Provenance: formalization of a published result. Source: arXiv:2610.37187, Section 2

The maximal real part s(Φ) of an eigenvalue of a linear map Φ on d × d complex matrices is the supremum of the real parts of the elements in the complex spectrum of Φ.
-/

/-- The maximal real part s(Φ) of an eigenvalue of a linear map Φ on d × d complex matrices is the supremum of the real parts of elements in the spectrum of Φ. -/
noncomputable def spectral_max_re (d : ℕ) (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) : ℝ := sSup (Complex.re '' spectrum ℂ Φ)
