import AFTD.Prelude
import AFTD.Kb.Tcs.LinearFlatteningTestable
import AFTD.Kb.Tcs.NotSumPureOfLinearFlatteningPotencyGt
import AFTD.Kb.Tcs.Tensor3Pure
import AFTD.Kb.Tcs.LinearFlatteningPotencyGt

/-!
# linear_flattening_testable_tensor_rank_gt

Topic: algebraic_complexity   Node: f006696eed54

Provenance: helper lemma. arXiv:2610.08504 Sec. 1

If the secant variety σ_r((ℂⁿ)⊗³) is testable by the linear flattening method, then there exists a tensor in (ℂⁿ)⊗³ that cannot be written as a sum of r pure tensors.
-/

/-- If order r is testable by linear flattenings, there exists a tensor in (ℂⁿ)⊗³ with tensor rank strictly greater than r. -/
theorem linear_flattening_testable_tensor_rank_gt {n r : ℕ}
    (h : linear_flattening_testable n r) :
    ∃ T : Fin n → Fin n → Fin n → ℂ,
      ∀ x y z : Fin r → Fin n → ℂ, T ≠ ∑ i, tensor3_pure (x i) (y i) (z i) := by
  rcases h with ⟨u, v, L, T, hT⟩
  exact ⟨T, not_sum_pure_of_linear_flattening_potency_gt L r T hT⟩
