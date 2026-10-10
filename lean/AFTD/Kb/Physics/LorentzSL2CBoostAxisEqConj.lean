import AFTD.Prelude
import AFTD.Kb.Physics.LorentzSL2CBoostAxis
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxis
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxisZeroMulDiagonalMulInv
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxisOneMulDiagonalMulInv
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxisTwoMulDiagonalMulInv
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxisZeroApply
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxisOneApply
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxisTwoApply
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxisZeroInvApply
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxisOneInvApply
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxisTwoInvApply
import AFTD.Kb.Physics.LorentzSL2CBoostAxisZeroApply
import AFTD.Kb.Physics.LorentzSL2CBoostAxisOneApply
import AFTD.Kb.Physics.LorentzSL2CBoostAxisTwoApply

/-!
# Lorentz.SL2C.boostAxis_eq_conj

Topic: special_relativity   Node: 21f224cf0c58

Provenance: formalization of a published result. Source: Physlib, `Lorentz.SL2C.boostAxis_eq_conj`. Lean proof by Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/LorentzGroup/Boosts/Axis.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Every axis boost is obtained by conjugating the `z`-axis boost by `rotationZToAxis`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix MatrixGroups in
/-- Every axis boost is obtained by conjugating the `z`-axis boost by `rotationZToAxis`. -/
lemma Lorentz.SL2C.boostAxis_eq_conj (i : Fin 3) (t : ℝ) (ht : t ≠ 0) :
    boostAxis i t ht =
      rotationZToAxis i * boostAxis 2 t ht * (rotationZToAxis i)⁻¹ := by
  fin_cases i
  · refine Subtype.ext ?_
    change !![((t : ℂ) + (t : ℂ)⁻¹) / 2, ((t : ℂ) - (t : ℂ)⁻¹) / 2;
        ((t : ℂ) - (t : ℂ)⁻¹) / 2, ((t : ℂ) + (t : ℂ)⁻¹) / 2] =
      (rotationZToAxis 0).1 * !![(t : ℂ), 0; 0, (t : ℂ)⁻¹] *
        ((rotationZToAxis 0)⁻¹).1
    rw [rotationZToAxis_zero_mul_diagonal_mul_inv]
  · refine Subtype.ext ?_
    change !![((t : ℂ) + (t : ℂ)⁻¹) / 2,
        -Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2;
        Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2,
        ((t : ℂ) + (t : ℂ)⁻¹) / 2] =
      (rotationZToAxis 1).1 * !![(t : ℂ), 0; 0, (t : ℂ)⁻¹] *
        ((rotationZToAxis 1)⁻¹).1
    rw [rotationZToAxis_one_mul_diagonal_mul_inv]
  · refine Subtype.ext ?_
    change !![(t : ℂ), 0; 0, (t : ℂ)⁻¹] =
      (rotationZToAxis 2).1 * !![(t : ℂ), 0; 0, (t : ℂ)⁻¹] *
        ((rotationZToAxis 2)⁻¹).1
    rw [rotationZToAxis_two_mul_diagonal_mul_inv]
