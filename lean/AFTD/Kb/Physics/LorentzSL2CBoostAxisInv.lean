import AFTD.Prelude
import AFTD.Kb.Physics.LorentzSL2CBoostAxis
import AFTD.Kb.Physics.LorentzSL2CBoostAxisZeroApply
import AFTD.Kb.Physics.LorentzSL2CBoostAxisOneApply
import AFTD.Kb.Physics.LorentzSL2CBoostAxisTwoApply

/-!
# Lorentz.SL2C.boostAxis_inv

Topic: special_relativity   Node: f05a8c32cf16

Provenance: formalization of a published result. Source: Physlib, `Lorentz.SL2C.boostAxis_inv`. Lean proof by Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/LorentzGroup/Boosts/Axis.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Inverting an axis boost replaces its multiplicative parameter `t` by `t⁻¹`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix MatrixGroups in
/-- Inverting an axis boost replaces its multiplicative parameter `t` by `t⁻¹`. -/
lemma Lorentz.SL2C.boostAxis_inv (i : Fin 3) (t : ℝ) (ht : t ≠ 0) :
    (boostAxis i t ht)⁻¹ = boostAxis i t⁻¹ (inv_ne_zero ht) := by
  fin_cases i
  · ext j k
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    fin_cases j <;> fin_cases k <;>
      simp [boostAxis, Complex.ofReal_inv, inv_inv] <;>
      ring
  · ext j k
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    fin_cases j <;> fin_cases k <;>
      simp [boostAxis, Complex.ofReal_inv, inv_inv] <;>
      ring
  · ext j k
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    fin_cases j <;> fin_cases k <;>
      simp [boostAxis, Complex.ofReal_inv, inv_inv]
