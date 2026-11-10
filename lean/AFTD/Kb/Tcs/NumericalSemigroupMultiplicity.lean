import AFTD.Prelude
import AFTD.Kb.Tcs.NumericalSemigroup

/-!
# numerical_semigroup_multiplicity

Topic: combinatorics   Node: 1924c68e3afc

Provenance: formalization of a published result. Source: arXiv:2611.11559

The multiplicity of a numerical semigroup S is the natural number defined as the infimum of its strictly positive elements: sInf {x ∈ (S.toAddSubmonoid : Set ℕ) | 0 < x}.
-/

/-- The multiplicity of a numerical semigroup is its smallest positive element. -/
noncomputable def numerical_semigroup_multiplicity (S : NumericalSemigroup) : ℕ := sInf {x ∈ (S.toAddSubmonoid : Set ℕ) | 0 < x}
