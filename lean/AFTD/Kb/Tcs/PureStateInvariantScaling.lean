import AFTD.Prelude
import AFTD.Kb.Tcs.IsQuadraticPureStateInvariant
import AFTD.Kb.Tcs.IsPureState
import AFTD.Kb.Tcs.QuadraticPureStateForm

/-!
# pure_state_invariant_scaling

Topic: quantum   Node: 89e89490c2a2

Provenance: helper lemma. arXiv:2610.36076 Sec. 3.1

For any family of matrices T, if zeta : Fin (d^2 - 1) → ℝ satisfies is_quadratic_pure_state_invariant T zeta, then for any real number alpha, alpha • zeta also satisfies is_quadratic_pure_state_invariant T (alpha • zeta).
-/

/-- The set of quadratic pure-state invariants is closed under scalar multiplication. -/
theorem pure_state_invariant_scaling {d : ℕ} (T : Fin (d^2 - 1) → Matrix (Fin d) (Fin d) ℂ)
    (ζ : Fin (d^2 - 1) → ℝ) (hζ : is_quadratic_pure_state_invariant T ζ) (α : ℝ) :
    is_quadratic_pure_state_invariant T (α • ζ) := by
  rcases hζ with ⟨c, hc⟩
  refine ⟨α * c, fun ρ hρ => ?_⟩
  unfold quadratic_pure_state_form
  simp_rw [Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [← Finset.mul_sum]
  exact congrArg (α * ·) (hc ρ hρ)
