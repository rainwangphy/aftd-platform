import AFTD.Prelude

/-!
# NumericalSemigroup

Topic: combinatorics   Node: 89eaed3dfef3

Provenance: formalization of a published result. Source: arXiv:2611.11559

A numerical semigroup is an additive submonoid of the natural numbers whose complement in ℕ is finite.
-/

/-- A numerical semigroup is an additive submonoid of ℕ with finite complement. -/
structure NumericalSemigroup extends AddSubmonoid ℕ where
  finite_compl : ((toAddSubmonoid : Set ℕ)ᶜ).Finite
