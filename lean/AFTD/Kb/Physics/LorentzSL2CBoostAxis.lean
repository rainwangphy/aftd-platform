import AFTD.Prelude

/-!
# Lorentz.SL2C.boostAxis

Topic: special_relativity   Node: be796d0a4bfe

Provenance: formalization of a published result. Source: Physlib, `Lorentz.SL2C.boostAxis`. Lean proof by Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/LorentzGroup/Boosts/Axis.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The `SL(2,ℂ)` lift of the boost along spatial axis `i`, with `0 = x`, `1 = y`, and `2 = z`. The parameter `t` is multiplicative, and for `t > 0` the rapidity is `2 * log t`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix MatrixGroups in
/-- The `SL(2,ℂ)` lift of the boost along spatial axis `i`, with `0 = x`, `1 = y`, and `2 = z`. The parameter `t` is multiplicative, and for `t > 0` the rapidity is `2 * log t`. -/
noncomputable def Lorentz.SL2C.boostAxis : Fin 3 → (t : ℝ) → t ≠ 0 → SL(2,ℂ)
  | 0, t, ht =>
      ⟨!![((t : ℂ) + (t : ℂ)⁻¹) / 2, ((t : ℂ) - (t : ℂ)⁻¹) / 2;
          ((t : ℂ) - (t : ℂ)⁻¹) / 2, ((t : ℂ) + (t : ℂ)⁻¹) / 2], by
        have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
        rw [Matrix.det_fin_two_of]
        field_simp
        ring⟩
  | 1, t, ht =>
      ⟨!![((t : ℂ) + (t : ℂ)⁻¹) / 2, -Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2;
          Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2, ((t : ℂ) + (t : ℂ)⁻¹) / 2], by
        have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
        have h2 : -Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2 *
            (Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2) =
            ((t : ℂ) - (t : ℂ)⁻¹) / 2 * (((t : ℂ) - (t : ℂ)⁻¹) / 2) := by
          have hI : -Complex.I * Complex.I = 1 := by
            rw [neg_mul, Complex.I_mul_I, neg_neg]
          calc -Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2 *
                (Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2)
              = (-Complex.I * Complex.I) *
                  (((t : ℂ) - (t : ℂ)⁻¹) / 2 * (((t : ℂ) - (t : ℂ)⁻¹) / 2)) := by
                ring
            _ = ((t : ℂ) - (t : ℂ)⁻¹) / 2 * (((t : ℂ) - (t : ℂ)⁻¹) / 2) := by
                rw [hI, one_mul]
        rw [Matrix.det_fin_two_of, h2]
        field_simp
        ring⟩
  | 2, t, ht =>
      ⟨!![(t : ℂ), 0; 0, (t : ℂ)⁻¹], by
        have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
        rw [Matrix.det_fin_two_of]
        simp [mul_inv_cancel₀ htc]⟩
