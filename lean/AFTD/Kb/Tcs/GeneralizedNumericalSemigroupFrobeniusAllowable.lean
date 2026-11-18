import AFTD.Prelude
import AFTD.Kb.Tcs.GeneralizedNumericalSemigroup
import AFTD.Kb.Tcs.GeneralizedNumericalSemigroupGaps

/-!
# generalized_numerical_semigroup_frobenius_allowable

Topic: combinatorics   Node: d1eef3ab2c3c

Provenance: formalization of a published result. Source: arXiv:2611.20086 Section 2

The Frobenius allowable elements of a generalized numerical semigroup S are the maximal elements of its gap set with respect to the pointwise partial order on ℕ^d.
-/

/-- The finite set of Frobenius allowable elements (maximal gaps) of S. -/
noncomputable def generalized_numerical_semigroup_frobenius_allowable {d : ℕ} (S : GeneralizedNumericalSemigroup d) : Finset (Fin d → ℕ) := by
  classical
  exact (generalized_numerical_semigroup_gaps S).filter
    (fun h => ∀ h' ∈ generalized_numerical_semigroup_gaps S, h ≤ h' → h = h')
