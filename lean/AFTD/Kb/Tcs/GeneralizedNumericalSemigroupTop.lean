import AFTD.Prelude
import AFTD.Kb.Tcs.GeneralizedNumericalSemigroup

/-!
# generalized_numerical_semigroup_top

Topic: combinatorics   Node: 82d2e89495e3

Provenance: formalization of a published result. Source: arXiv:2611.20086 Section 2

The submonoid of all elements of ℕ^d is a generalized numerical semigroup with empty complement.
-/

/-- The full generalized numerical semigroup on `Fin d → ℕ`. -/
def generalized_numerical_semigroup_top (d : ℕ) : GeneralizedNumericalSemigroup d where
  toAddSubmonoid := ⊤
  finite_compl := by simp
