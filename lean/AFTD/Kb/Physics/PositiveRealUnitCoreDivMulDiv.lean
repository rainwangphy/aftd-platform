import AFTD.Prelude
import AFTD.Kb.Physics.PositiveRealUnitCore
import AFTD.Kb.Physics.PositiveRealUnitCoreInstHDiv
import AFTD.Kb.Physics.PositiveRealUnitCoreValNeZero
import AFTD.Kb.Physics.PositiveRealUnitCoreDivPos
import AFTD.Kb.Physics.PositiveRealUnitCoreDivNeZero
import AFTD.Kb.Physics.PositiveRealUnitCoreDivSelf

/-!
# PositiveRealUnitCore.div_mul_div

Topic: classical_mechanics   Node: ec42ad2b2745

Provenance: formalization of a published result. Source: Physlib, `PositiveRealUnitCore.div_mul_div`. Lean proof by Joseph Tooby-Smith, Hirotaka Monya, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/PositiveRealUnit.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Unit ratios compose along an intermediate choice of unit.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open PositiveRealUnitCore in
open NNReal in
variable {U : Type} [PositiveRealUnitCore U] in
/-- Unit ratios compose along an intermediate choice of unit. -/
lemma PositiveRealUnitCore.div_mul_div (x y z : U) : (x / y : NNReal) * (y / z) = x / z := by
  apply NNReal.eq
  change val x / val y * (val y / val z) = val x / val z
  rw [div_mul_div_comm, mul_comm (val x) (val y),
    mul_div_mul_left _ _ (val_ne_zero y)]
