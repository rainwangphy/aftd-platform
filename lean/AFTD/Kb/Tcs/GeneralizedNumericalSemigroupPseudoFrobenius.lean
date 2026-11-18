import AFTD.Prelude
import AFTD.Kb.Tcs.GeneralizedNumericalSemigroup
import AFTD.Kb.Tcs.GeneralizedNumericalSemigroupGaps

/-!
# generalized_numerical_semigroup_pseudo_frobenius

Topic: combinatorics   Node: 16f804f221e8

Provenance: formalization of a published result. Source: arXiv:2611.20086 Definition 2.4

The pseudo-Frobenius elements of a generalized numerical semigroup S are the gaps h of S such that h + s ∈ S for every non-zero s ∈ S.
-/

/-- The finite set of pseudo-Frobenius elements of a generalized numerical semigroup S. -/
noncomputable def generalized_numerical_semigroup_pseudo_frobenius {d : ℕ} (S : GeneralizedNumericalSemigroup d) : Finset (Fin d → ℕ) := by
  classical
  exact (generalized_numerical_semigroup_gaps S).filter
    (fun h => ∀ s ∈ S.toAddSubmonoid, s ≠ 0 → h + s ∈ S.toAddSubmonoid)
