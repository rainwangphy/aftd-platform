import AFTD.Prelude
import AFTD.Kb.Physics.PositiveRealUnitCore
import AFTD.Kb.Physics.PositiveRealUnitCoreValNeZero
import AFTD.Kb.Physics.PositiveRealUnitCoreDivPos
import AFTD.Kb.Physics.PositiveRealUnitCoreDivNeZero
import AFTD.Kb.Physics.PositiveRealUnitCoreDivSelf
import AFTD.Kb.Physics.PositiveRealUnitCoreDivMulDivCoe

/-!
# PositiveRealUnitCore.scale

Topic: classical_mechanics   Node: 7d5f350e1953

Provenance: formalization of a published result. Source: Physlib, `PositiveRealUnitCore.scale`. Lean proof by Joseph Tooby-Smith, Hirotaka Monya, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/PositiveRealUnit.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Rescale a unit by a strictly positive real factor.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
variable {U : Type} [PositiveRealUnitCore U] in
/-- Rescale a unit by a strictly positive real factor. -/
def PositiveRealUnitCore.scale (r : ℝ) (x : U) (hr : 0 < r := by norm_num) : U :=
  ofVal (r * val x) (mul_pos hr (pos x))
