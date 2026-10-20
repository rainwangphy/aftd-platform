import AFTD.Prelude
import AFTD.Kb.Tcs.LinearFlatteningTestable
import AFTD.Kb.Tcs.Tensor3Pure
import AFTD.Kb.Tcs.LinearFlatteningPotencyGt

/-!
# linear_flattening_testable_of_rank_le

Topic: algebraic_complexity   Node: bafc70f55958

Provenance: helper lemma. step towards op100_linear_flattening_potency_gt_even

If a linear flattening L on (ℂⁿ)⊗³ satisfies rank L(x ⊗ y ⊗ z) ≤ ρ for all x, y, z and rank L(T) > r * ρ for some tensor T, then the secant variety σ_r((ℂⁿ)⊗³) is testable by the linear flattening method.
-/

/-- A sufficient condition for secant variety testability by linear flattenings: if rank L(x ⊗ y ⊗ z) ≤ ρ for all pure tensors and rank L(T) > r * ρ for some tensor T, then σ_r is testable. -/
theorem linear_flattening_testable_of_rank_le (n u v : ℕ)
    (L : (Fin n → Fin n → Fin n → ℂ) →ₗ[ℂ] Matrix (Fin u) (Fin v) ℂ) (r ρ : ℕ)
    (hρ : ∀ x y z : Fin n → ℂ, (L (tensor3_pure x y z)).rank ≤ ρ)
    (T : Fin n → Fin n → Fin n → ℂ)
    (hT : r * ρ < (L T).rank) :
    linear_flattening_testable n r := ⟨u, v, L, T, fun x y z => lt_of_le_of_lt (Nat.mul_le_mul_left r (hρ x y z)) hT⟩
