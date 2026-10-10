import AFTD.Prelude
import AFTD.Kb.Physics.PositiveRealUnitCore
import AFTD.Kb.Physics.PositiveRealUnitCoreValNeZero
import AFTD.Kb.Physics.PositiveRealUnitCoreDivPos
import AFTD.Kb.Physics.PositiveRealUnitCoreDivNeZero
import AFTD.Kb.Physics.PositiveRealUnitCoreDivSelf
import AFTD.Kb.Physics.PositiveRealUnitCoreDivMulDivCoe
import AFTD.Kb.Physics.PositiveRealUnitCoreScaleVal

/-!
# PositiveRealUnitCore.ext

Topic: classical_mechanics   Node: 326b836c2fa5

Provenance: formalization of a published result. Source: Physlib, `PositiveRealUnitCore.ext`. Lean proof by Joseph Tooby-Smith, Hirotaka Monya, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/PositiveRealUnit.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Units with equal magnitudes are equal.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
variable {U : Type} [PositiveRealUnitCore U] in
/-- Units with equal magnitudes are equal. -/
lemma PositiveRealUnitCore.ext {x y : U} (h : val x = val y) : x = y := by
  rw [← ofVal_val x, ← ofVal_val y]
  congr
