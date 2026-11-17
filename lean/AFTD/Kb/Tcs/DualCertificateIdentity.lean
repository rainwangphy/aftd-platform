import AFTD.Prelude
import AFTD.Kb.Tcs.SignedRelation
import AFTD.Kb.Tcs.DualCertPBounds
import AFTD.Kb.Tcs.SignedRelationStepBasisTriangular
import AFTD.Kb.Tcs.SignedRelationStepBasisDualSolution
import AFTD.Kb.Tcs.SignedRelationLinearCombinationOfStepBasis

/-!
# dual_certificate_identity

Topic: combinatorics   Node: e94a072713b6

Provenance: formalization of a published result. Source: arXiv:2611.17360 Theorem 3.2 (i) and Step 1

For every natural number n with 1 ≤ n, there exists a sequence of integers y : Fin n → ℤ with 1 ≤ y j for all j : Fin n, such that for all x : Fin n → ℝ, the linear combination ∑ j : Fin n, (y j : ℝ) * signed_relation n (j.val + 1) x equals the last coordinate x ⟨n - 1, by omega⟩.
-/

/-- Existence of positive integer multipliers summing the signed relations to the last coordinate. -/
theorem dual_certificate_identity (n : ℕ) (hn : 1 ≤ n) :
    ∃ y : Fin n → ℤ, (∀ j : Fin n, 1 ≤ y j) ∧
      ∀ x : Fin n → ℝ, (∑ j : Fin n, (y j : ℝ) * signed_relation n (j.val + 1) x) = x ⟨n - 1, by omega⟩ := by
  obtain ⟨y, hy1, hy⟩ := signed_relation_step_basis_dual_solution n hn
  exact ⟨y, hy1, signed_relation_linear_combination_of_step_basis n hn (fun j => (y j : ℝ)) hy⟩
