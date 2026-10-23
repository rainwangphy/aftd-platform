import AFTD.Prelude
import AFTD.Kb.Tcs.LinearFlatteningPotencyGt
import AFTD.Kb.Tcs.Tensor3Pure

/-!
# linear_flattening_potency_gt_of_rank_le

Topic: algebraic_complexity   Node: 7c8870f73c5d

Provenance: helper lemma. step towards linear_flattening_testable_order_gap_four

If a linear flattening L on (ℂⁿ)⊗³ satisfies rank L(x ⊗ y ⊗ z) ≤ ρ for all x, y, z and rank L(T) > r * ρ for some tensor T, then L has potency strictly greater than r.
-/

/-- A linear flattening L achieves potency strictly greater than r if there is a tensor T with rank L(T) > r * ρ for a uniform upper bound ρ on the rank of L on all pure tensors. -/
theorem linear_flattening_potency_gt_of_rank_le {n u v : ℕ}
    (L : (Fin n → Fin n → Fin n → ℂ) →ₗ[ℂ] Matrix (Fin u) (Fin v) ℂ) (r ρ : ℕ)
    (hρ : ∀ x y z : Fin n → ℂ, (L (tensor3_pure x y z)).rank ≤ ρ)
    (T : Fin n → Fin n → Fin n → ℂ)
    (hT : r * ρ < (L T).rank) :
    linear_flattening_potency_gt L r :=
  ⟨T, fun x y z => lt_of_le_of_lt (Nat.mul_le_mul_left r (hρ x y z)) hT⟩
