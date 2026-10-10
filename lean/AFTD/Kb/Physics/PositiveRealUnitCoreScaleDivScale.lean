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
import AFTD.Kb.Physics.PositiveRealUnitCoreSelfDivScale
import AFTD.Kb.Physics.PositiveRealUnitCoreScaleOne

/-!
# PositiveRealUnitCore.scale_div_scale

Topic: classical_mechanics   Node: eb492db36a7a

Provenance: formalization of a published result. Source: Physlib, `PositiveRealUnitCore.scale_div_scale`. Lean proof by Joseph Tooby-Smith, Hirotaka Monya, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/PositiveRealUnit.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Rescaling two units multiplies their ratio by the ratio of the factors.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open PositiveRealUnitCore in
open NNReal in
variable {U : Type} [PositiveRealUnitCore U] in
/-- Rescaling two units multiplies their ratio by the ratio of the factors. -/
@[simp]
lemma PositiveRealUnitCore.scale_div_scale (x1 x2 : U) {r1 r2 : ℝ} (hr1 : 0 < r1) (hr2 : 0 < r2) :
    scale r1 x1 hr1 / scale r2 x2 hr2 =
      (⟨r1, le_of_lt hr1⟩ / ⟨r2, le_of_lt hr2⟩ : NNReal) * (x1 / x2) := by
  apply NNReal.eq
  change val (scale r1 x1 hr1) / val (scale r2 x2 hr2) =
    (r1 / r2) * (val x1 / val x2)
  rw [scale_val, scale_val]
  rw [div_mul_div_comm]
