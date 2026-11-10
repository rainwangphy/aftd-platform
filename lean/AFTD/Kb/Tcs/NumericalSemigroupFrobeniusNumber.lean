import AFTD.Prelude
import AFTD.Kb.Tcs.NumericalSemigroup

/-!
# numerical_semigroup_frobenius_number

Topic: combinatorics   Node: 615944d21d4d

Provenance: formalization of a published result. Source: arXiv:2611.11559

The Frobenius number of a numerical semigroup S is the natural number defined as the supremum of the complement of S in ℕ: sSup ((S.toAddSubmonoid : Set ℕ)ᶜ).
-/

/-- The Frobenius number of a numerical semigroup is the supremum of its complement in ℕ. -/
noncomputable def numerical_semigroup_frobenius_number (S : NumericalSemigroup) : ℕ := sSup ((S.toAddSubmonoid : Set ℕ)ᶜ)
