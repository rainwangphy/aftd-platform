import AFTD.Prelude
import AFTD.Kb.Tcs.IsQuadraticPureStateInvariant
import AFTD.Kb.Tcs.IsPureState
import AFTD.Kb.Tcs.QuadraticPureStateForm

/-!
# pure_state_invariant_addition

Topic: quantum   Node: 30b9055fa027

Provenance: helper lemma. arXiv:2610.36076 Sec. 3.1

For any family of matrices T and weight vectors zeta_1, zeta_2 : Fin (d^2 - 1) → ℝ, if both satisfy is_quadratic_pure_state_invariant T, then their sum zeta_1 + zeta_2 also satisfies is_quadratic_pure_state_invariant T (zeta_1 + zeta_2).
-/

/-- The set of quadratic pure-state invariants is closed under addition, forming a subspace of R^(d^2-1). -/
theorem pure_state_invariant_addition {d : ℕ} (T : Fin (d^2 - 1) → Matrix (Fin d) (Fin d) ℂ)
    (ζ₁ ζ₂ : Fin (d^2 - 1) → ℝ)
    (h₁ : is_quadratic_pure_state_invariant T ζ₁)
    (h₂ : is_quadratic_pure_state_invariant T ζ₂) :
    is_quadratic_pure_state_invariant T (ζ₁ + ζ₂) := by
  obtain ⟨c₁, hc₁⟩ := h₁
  obtain ⟨c₂, hc₂⟩ := h₂
  refine ⟨c₁ + c₂, fun ρ hρ => ?_⟩
  have e₁ := hc₁ ρ hρ
  have e₂ := hc₂ ρ hρ
  unfold quadratic_pure_state_form at e₁ e₂ ⊢
  simp_rw [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  rw [e₁, e₂]
