import AFTD.Prelude

/-!
# redistribution_characteristic

Topic: mechanism_design   Node: bfa31448afb0

Provenance: helper lemma. Routine finite-characteristic-function helper for IN-251, arXiv:2610.10995 Lemma4.3 Steps1/2 and equation12. These statements do not assert the half-plane boundary integral inequality or the main harmonic error bound. No research advance.

The empirical characteristic function continued to the complex plane: the normalized finite sum of exp(i*z*θ_j).
-/

open Finset MeasureTheory

noncomputable def redistribution_characteristic {n : ℕ} (θ : Fin n → ℝ) (z : ℂ) : ℂ := (1 / (n : ℂ)) * ∑ j, Complex.exp (Complex.I * z * (θ j : ℂ))
