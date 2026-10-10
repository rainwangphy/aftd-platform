import AFTD.Prelude
import AFTD.Kb.Physics.LorentzSL2CBoostAxis
import AFTD.Kb.Physics.LorentzSL2CBoostAxisZeroApply

/-!
# Lorentz.SL2C.boostAxis_one_apply

Topic: special_relativity   Node: ed7c14b9f315

Provenance: formalization of a published result. Source: Physlib, `Lorentz.SL2C.boostAxis_one_apply`. Lean proof by Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/LorentzGroup/Boosts/Axis.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The matrix entries of the `SL(2,ℂ)` boost lift along the `y`-axis.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix MatrixGroups in
/-- The matrix entries of the `SL(2,ℂ)` boost lift along the `y`-axis. -/
@[simp] lemma Lorentz.SL2C.boostAxis_one_apply (t : ℝ) (ht : t ≠ 0) (j k : Fin 2) :
    (boostAxis 1 t ht).1 j k =
      (!![((t : ℂ) + (t : ℂ)⁻¹) / 2,
        -Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2;
        Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2,
        ((t : ℂ) + (t : ℂ)⁻¹) / 2]) j k := rfl
