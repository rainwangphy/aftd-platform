import AFTD.Prelude

/-!
# energy_filter_fourier_symbol

Topic: statistical_mechanics   Node: bf06f5b7997d

Provenance: formalization of a published result. Source: knowledgebase, OP-1115

For a sequence a : ℤ → ℝ and real θ, energy_filter_fourier_symbol a θ is the Fourier symbol A(θ) = ∑' j : ℤ, (a j : ℂ) * Complex.exp (Complex.I * (j : ℝ) * θ).
-/

/-- The discrete-time Fourier symbol A(θ) = ∑_j a_j exp(i j θ) of a filter sequence a. -/
noncomputable def energy_filter_fourier_symbol (a : ℤ → ℝ) (θ : ℝ) : ℂ := ∑' j : ℤ, (a j : ℂ) * Complex.exp (Complex.I * (j : ℝ) * (θ : ℝ))
