import AFTD.Prelude

/-!
# GeneralizedNumericalSemigroup

Topic: combinatorics   Node: 3c15e24fdafa

Provenance: formalization of a published result. Source: arXiv:2611.20086 Definition 2.1

A generalized numerical semigroup in dimension d is an additive submonoid of ℕ^d whose complement in ℕ^d is finite.
-/

/-- An additive submonoid of `Fin d → ℕ` with finite complement. -/
structure GeneralizedNumericalSemigroup (d : ℕ) extends AddSubmonoid (Fin d → ℕ) where
  finite_compl : (↑toAddSubmonoid : Set (Fin d → ℕ))ᶜ.Finite
