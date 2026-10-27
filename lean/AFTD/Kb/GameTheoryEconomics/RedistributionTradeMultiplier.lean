import AFTD.Prelude

/-!
# redistribution_trade_multiplier

Topic: mechanism_design   Node: 3be4d75421bf

Provenance: helper lemma. Routine helper in the proof of arXiv:2610.10995, Lemmas4.2/4.3 and equations11/12/20/21. Added while working IN-251. No research advance; the main harmonic bound remains unproved.

The real nonnegative Fourier multiplier of the symmetric trade operator: the square of the mean cosine plus the square of the mean sine of the report phases.
-/

open Finset MeasureTheory

noncomputable def redistribution_trade_multiplier {n : ℕ} (θ : Fin n → ℝ) (u : ℝ) : ℝ := ((∑ j, Real.cos (u * θ j)) / (n : ℝ))^2 + ((∑ j, Real.sin (u * θ j)) / (n : ℝ))^2
