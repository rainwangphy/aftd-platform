import AFTD.Prelude

/-!
# overcomplete_ica_empirical_fourth_moment

Topic: estimation   Node: b4d4b85bb11c

Provenance: formalization of a published result. Source: arXiv:2611.11852 Sec. 5

For a sample of n observations X_1, ..., X_n in the complex plane, the empirical fourth moment of their norms is (1/n) * sum_{i=1}^n ||X_i||^4.
-/

/-- Empirical fourth moment of the Euclidean norm of a sample in the complex plane. -/
noncomputable def overcomplete_ica_empirical_fourth_moment (n : ℕ) (X : Fin n → ℂ) : ℝ := (1 / (n : ℝ)) * ∑ i : Fin n, ‖X i‖ ^ 4
