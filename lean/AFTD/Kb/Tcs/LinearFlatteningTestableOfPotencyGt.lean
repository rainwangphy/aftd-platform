import AFTD.Prelude
import AFTD.Kb.Tcs.LinearFlatteningTestable
import AFTD.Kb.Tcs.LinearFlatteningPotencyGt

/-!
# linear_flattening_testable_of_potency_gt

Topic: algebraic_complexity   Node: 0cc098fe6986

Provenance: helper lemma. step towards linear_flattening_testable_order_gap_four

If a linear flattening L : (ℂⁿ)⊗³ → Mat_{u×v}(ℂ) has potency strictly greater than r, then (ℂⁿ)⊗³ is testable at order r by the linear flattening method.
-/

/-- A tensor space (ℂⁿ)⊗³ is testable at order r if there exists an explicit linear flattening L achieving potency strictly greater than r. -/
theorem linear_flattening_testable_of_potency_gt {n u v : ℕ}
    (L : (Fin n → Fin n → Fin n → ℂ) →ₗ[ℂ] Matrix (Fin u) (Fin v) ℂ) (r : ℕ)
    (h : linear_flattening_potency_gt L r) :
    linear_flattening_testable n r := ⟨u, v, L, h⟩
