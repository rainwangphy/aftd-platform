import AFTD.Prelude

/-!
# is_gibbs_stochastic

Topic: submodular   Node: 4cae134f1787

Provenance: formalization of a published result. Source: arXiv:2610.35433

A square transition matrix T on n microstates is Gibbs-stochastic with respect to an equilibrium probability vector γ if its entries are non-negative, each column sums to 1, and it preserves γ.
-/

/-- A Gibbs-stochastic matrix is a column-stochastic matrix preserving the background equilibrium distribution γ. -/
def is_gibbs_stochastic {n : ℕ} (γ : Fin n → ℝ) (T : Fin n → Fin n → ℝ) : Prop := (∀ i j, 0 ≤ T i j) ∧ (∀ j, ∑ i, T i j = 1) ∧ (∀ i, ∑ j, T i j * γ j = γ i)
