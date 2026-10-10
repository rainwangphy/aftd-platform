import AFTD.Prelude
import AFTD.Kb.Physics.PositiveRealUnitCore
import AFTD.Kb.Physics.PositiveRealUnitCoreInstHDiv
import AFTD.Kb.Physics.PositiveRealUnitCoreScale
import AFTD.Kb.Physics.PositiveRealUnitCoreExt
import AFTD.Kb.Physics.PositiveRealUnitCoreScaleVal
import AFTD.Kb.Physics.PositiveRealUnitCoreValNeZero
import AFTD.Kb.Physics.PositiveRealUnitCoreDivPos
import AFTD.Kb.Physics.PositiveRealUnitCoreDivNeZero
import AFTD.Kb.Physics.PositiveRealUnitCoreDivSelf
import AFTD.Kb.Physics.PositiveRealUnitCoreDivMulDivCoe
import AFTD.Kb.Physics.PositiveRealUnitCoreScaleDivSelf
import AFTD.Kb.Physics.PositiveRealUnitCoreSelfDivScale
import AFTD.Kb.Physics.PositiveRealUnitCoreScaleOne
import AFTD.Kb.Physics.PositiveRealUnitCoreScaleDivScale
import AFTD.Kb.Physics.PositiveRealUnitCoreScaleScale

/-!
# PositiveRealUnitCore.scale_div

Topic: classical_mechanics   Node: 71c01260addd

Provenance: formalization of a published result. Source: Physlib, `PositiveRealUnitCore.scale_div`. Lean proof by Joseph Tooby-Smith, Hirotaka Monya, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/PositiveRealUnit.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Rescaling a unit by the ratio to a target unit produces that target.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open PositiveRealUnitCore in
open NNReal in
variable {U : Type} [PositiveRealUnitCore U] in
/-- Rescaling a unit by the ratio to a target unit produces that target. -/
@[simp]
lemma PositiveRealUnitCore.scale_div (x y : U) (hr : 0 < (y / x : ℝ)) :
    scale (y / x) x hr = y := by
  apply ext
  rw [scale_val]
  change (val y / val x) * val x = val y
  field_simp [val_ne_zero]
