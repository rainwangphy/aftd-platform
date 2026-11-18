import AFTD.Prelude
import AFTD.Kb.Tcs.GeneralizedNumericalSemigroup
import AFTD.Kb.Tcs.GeneralizedNumericalSemigroupGaps

/-!
# generalized_numerical_semigroup_non_gaps_below_gaps

Topic: combinatorics   Node: 34ec6343824a

Provenance: formalization of a published result. Source: arXiv:2611.20086 Section 5

The set of non-gaps below gaps of a generalized numerical semigroup S is the finite set of elements of S bounded above in the pointwise partial order by some gap of S.
-/

/-- The finite set N(S) of non-gaps bounded above by at least one gap of S. -/
noncomputable def generalized_numerical_semigroup_non_gaps_below_gaps {d : ℕ} (S : GeneralizedNumericalSemigroup d) : Finset (Fin d → ℕ) := by
  classical
  exact ((generalized_numerical_semigroup_gaps S).biUnion Finset.Iic).filter
    (fun x => x ∈ S.toAddSubmonoid)
