import AFTD.Prelude
import AFTD.Kb.Physics.PositiveRealUnitCore
import AFTD.Kb.Physics.PositiveRealUnitCoreInstHDiv
import AFTD.Kb.Physics.PositiveRealUnitCoreScale
import AFTD.Kb.Physics.PositiveRealUnitCoreScaleVal
import AFTD.Kb.Physics.PositiveRealUnitCoreValNeZero
import AFTD.Kb.Physics.PositiveRealUnitCoreDivPos
import AFTD.Kb.Physics.PositiveRealUnitCoreDivNeZero
import AFTD.Kb.Physics.PositiveRealUnitCoreDivSelf
import AFTD.Kb.Physics.PositiveRealUnitCoreDivMulDivCoe
import AFTD.Kb.Physics.PositiveRealUnitCoreScaleDivSelf

/-!
# PositiveRealUnitCore.self_div_scale

Topic: classical_mechanics   Node: e0badc484313

Provenance: formalization of a published result. Source: Physlib, `PositiveRealUnitCore.self_div_scale`. Lean proof by Joseph Tooby-Smith, Hirotaka Monya, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/PositiveRealUnit.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The reverse ratio is the reciprocal of the scaling factor.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open PositiveRealUnitCore in
open NNReal in
variable {U : Type} [PositiveRealUnitCore U] in
/-- The reverse ratio is the reciprocal of the scaling factor. -/
@[simp]
lemma PositiveRealUnitCore.self_div_scale (x : U) (r : ℝ) (hr : 0 < r) :
    x / scale r x hr =
      (⟨1 / r, _root_.div_nonneg (by simp) (le_of_lt hr)⟩ : NNReal) := by
  apply NNReal.eq
  change val x / val (scale r x hr) = 1 / r
  rw [scale_val]
  field_simp [val_ne_zero, ne_of_gt hr]
