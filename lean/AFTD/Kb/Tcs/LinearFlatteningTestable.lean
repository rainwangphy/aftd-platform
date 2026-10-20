import AFTD.Prelude
import AFTD.Kb.Tcs.LinearFlatteningPotencyGt

/-!
# linear_flattening_testable

Topic: algebraic_complexity   Node: 9e562af9faeb

Provenance: formalization of a published result. Source: arXiv:2610.08504 Sec. 1

The secant variety σ_r((ℂⁿ)⊗³) is testable by the linear flattening method if there exists a linear flattening L : (ℂⁿ)⊗³ → Mat_{u×v}(ℂ) with potency strictly greater than r.
-/

/-- A secant variety order r is testable by the linear flattening method on (ℂⁿ)⊗³: some linear flattening achieves potency strictly greater than r. -/
def linear_flattening_testable (n : ℕ) (r : ℕ) : Prop := ∃ (u v : ℕ) (L : (Fin n → Fin n → Fin n → ℂ) →ₗ[ℂ] Matrix (Fin u) (Fin v) ℂ),
    linear_flattening_potency_gt L r
