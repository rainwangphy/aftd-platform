import AFTD.Prelude
import AFTD.Kb.Tcs.NumericalSemigroup

/-!
# numerical_semigroup_genus

Topic: combinatorics   Node: b8298ca7fd35

Provenance: formalization of a published result. Source: arXiv:2611.11559

The genus of a numerical semigroup S is the natural number defined as the cardinality of its complement in ℕ: Set.ncard ((S.toAddSubmonoid : Set ℕ)ᶜ).
-/

/-- The genus of a numerical semigroup is the cardinality of its complement in ℕ. -/
noncomputable def numerical_semigroup_genus (S : NumericalSemigroup) : ℕ := Set.ncard ((S.toAddSubmonoid : Set ℕ)ᶜ)
