import AFTD.Prelude
import AFTD.Kb.NumberTheory.IntToEuclidean

/-!
# is_rational_subspace

Topic: elementary_number_theory   Node: 77a7167c5068

Provenance: formalization of a published result. Source: arXiv:2610.37711, Definition 3.1

A linear subspace U in ℝ^n is rational if it is the real span of a set of integer vectors.
-/

/-- A linear subspace U in ℝ^n is rational if it is spanned by integer vectors. -/
def is_rational_subspace (n : ℕ) (U : Submodule ℝ (EuclideanSpace ℝ (Fin n))) : Prop := ∃ S : Set (Fin n → ℤ), U = Submodule.span ℝ (int_to_euclidean n '' S)
