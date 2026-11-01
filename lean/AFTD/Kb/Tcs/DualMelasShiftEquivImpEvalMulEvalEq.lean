import AFTD.Prelude
import AFTD.Kb.Tcs.DualMelasShiftEquiv

/-!
# dual_melas_shift_equiv_imp_eval_mul_eval_eq

Topic: information   Node: b9c6d1c57b3d

Provenance: helper lemma. arXiv:2610.38017 Lemma 5

If binary polynomials f and g are shift-equivalent modulo the product of the minimal polynomials of α and α⁻¹, and α is nonzero, then f(α) * f(α⁻¹) = g(α) * g(α⁻¹).
-/

/-- Shift-equivalent polynomials have equal product of evaluations at α and α⁻¹. -/
theorem dual_melas_shift_equiv_imp_eval_mul_eval_eq
    {F : Type*} [Field F] [Algebra (ZMod 2) F]
    (α : F) (hα : α ≠ 0) (f g : Polynomial (ZMod 2))
    (hsim : dual_melas_shift_equiv α f g) :
    Polynomial.aeval α f * Polynomial.aeval α⁻¹ f =
      Polynomial.aeval α g * Polynomial.aeval α⁻¹ g := by
  rcases hsim with ⟨j, q, hq⟩
  have h1 : Polynomial.aeval α (f - Polynomial.X ^ j * g) =
      Polynomial.aeval α (minpoly (ZMod 2) α * minpoly (ZMod 2) α⁻¹ * q) := by
    rw [hq]
  simp only [map_sub, map_mul, Polynomial.aeval_X_pow, minpoly.aeval, zero_mul] at h1
  have hα_eval : Polynomial.aeval α f = α ^ j * Polynomial.aeval α g := sub_eq_zero.mp h1
  have h2 : Polynomial.aeval α⁻¹ (f - Polynomial.X ^ j * g) =
      Polynomial.aeval α⁻¹ (minpoly (ZMod 2) α * minpoly (ZMod 2) α⁻¹ * q) := by
    rw [hq]
  simp only [map_sub, map_mul, Polynomial.aeval_X_pow, minpoly.aeval, mul_zero, zero_mul, inv_pow] at h2
  have hαinv_eval : Polynomial.aeval α⁻¹ f = (α ^ j)⁻¹ * Polynomial.aeval α⁻¹ g := sub_eq_zero.mp h2
  rw [hα_eval, hαinv_eval]
  have hpow_ne : α ^ j ≠ 0 := pow_ne_zero j hα
  calc
    (α ^ j * Polynomial.aeval α g) * ((α ^ j)⁻¹ * Polynomial.aeval α⁻¹ g)
      = (α ^ j * (α ^ j)⁻¹) * (Polynomial.aeval α g * Polynomial.aeval α⁻¹ g) := by ring
    _ = 1 * (Polynomial.aeval α g * Polynomial.aeval α⁻¹ g) := by rw [mul_inv_cancel₀ hpow_ne]
    _ = Polynomial.aeval α g * Polynomial.aeval α⁻¹ g := one_mul _
