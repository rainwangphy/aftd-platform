import AFTD.Prelude
import AFTD.Kb.Tcs.GeneralizedNumericalSemigroup

/-!
# generalized_numerical_semigroup_gaps

Topic: combinatorics   Node: b19e1be74095

Provenance: formalization of a published result. Source: arXiv:2611.20086 Definition 2.1

The set of gaps of a generalized numerical semigroup S is the finite set of elements of ℕ^d not belonging to S.
-/

/-- The finite set of gaps of a generalized numerical semigroup S. -/
noncomputable def generalized_numerical_semigroup_gaps {d : ℕ} (S : GeneralizedNumericalSemigroup d) : Finset (Fin d → ℕ) := S.finite_compl.toFinset
