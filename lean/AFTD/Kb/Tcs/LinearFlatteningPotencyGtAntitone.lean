import AFTD.Prelude
import AFTD.Kb.Tcs.LinearFlatteningPotencyGt
import AFTD.Kb.Tcs.Tensor3Pure

/-!
# linear_flattening_potency_gt_antitone

Topic: algebraic_complexity   Node: 19c34799d9c9

Provenance: helper lemma. arXiv:2610.08504 Sec. 1

If a linear flattening L on (ℂⁿ)⊗³ has potency strictly greater than r, then for any r' ≤ r it also has potency strictly greater than r'.
-/

/-- If a linear flattening has potency greater than r, it also has potency greater than any r' ≤ r. -/
theorem linear_flattening_potency_gt_antitone {n u v : ℕ}
    (L : (Fin n → Fin n → Fin n → ℂ) →ₗ[ℂ] Matrix (Fin u) (Fin v) ℂ)
    {r r' : ℕ} (hr : r' ≤ r) (h : linear_flattening_potency_gt L r) :
    linear_flattening_potency_gt L r' := by
  rcases h with ⟨T, hT⟩
  refine ⟨T, fun x y z => ?_⟩
  have h1 := hT x y z
  have h2 : r' * (L (tensor3_pure x y z)).rank ≤ r * (L (tensor3_pure x y z)).rank :=
    Nat.mul_le_mul_right _ hr
  exact lt_of_le_of_lt h2 h1
