import AFTD.Prelude

/-!
# relative_lorenz_curve

Topic: submodular   Node: 3ad5f6be78dd

Provenance: formalization of a published result. Source: arXiv:2610.35433:191; Lostaglio 2019; Ruch, Schoenhofer, Sloane 1978

Given a natural number n, vectors x, γ : Fin n → ℝ, and a parameter t : ℝ, the relative Lorenz curve relative_lorenz_curve x γ t is defined as the supremum (sSup) of ∑ i, α i * x i over all α : Fin n → ℝ satisfying 0 ≤ α i ∧ α i ≤ 1 for all i and ∑ i, α i * γ i ≤ t.
-/

/-- The relative Lorenz curve L_{x|γ}(t) of population vector x with respect to Gibbs vector γ. -/
noncomputable def relative_lorenz_curve {n : ℕ} (x γ : Fin n → ℝ) (t : ℝ) : ℝ := sSup ((fun α : Fin n → ℝ => ∑ i, α i * x i) ''
    {α : Fin n → ℝ | (∀ i, 0 ≤ α i ∧ α i ≤ 1) ∧ ∑ i, α i * γ i ≤ t})
