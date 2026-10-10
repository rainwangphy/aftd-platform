import AFTD.Prelude
import AFTD.Kb.Physics.PositiveRealUnitCore
import AFTD.Kb.Physics.PositiveRealUnitCoreInstHDiv
import AFTD.Kb.Physics.PositiveRealUnitCoreValNeZero
import AFTD.Kb.Physics.PositiveRealUnitCoreDivPos
import AFTD.Kb.Physics.PositiveRealUnitCoreDivNeZero
import AFTD.Kb.Physics.PositiveRealUnitCoreDivSelf

/-!
# PositiveRealUnitCore.div_mul_div_coe

Topic: classical_mechanics   Node: 358861657683

Provenance: formalization of a published result. Source: Physlib, `PositiveRealUnitCore.div_mul_div_coe`. Lean proof by Joseph Tooby-Smith, Hirotaka Monya, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/PositiveRealUnit.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

PositiveRealUnitCore.div_mul_div_coe
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open PositiveRealUnitCore in
open NNReal in
variable {U : Type} [PositiveRealUnitCore U] in
@[simp]
lemma PositiveRealUnitCore.div_mul_div_coe (x y z : U) :
    (x / y : ℝ) * (y / z : ℝ) = x / z := by
  change val x / val y * (val y / val z) = val x / val z
  field_simp [val_ne_zero]
