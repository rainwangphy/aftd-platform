import AFTD.Prelude
import AFTD.Kb.Physics.MassUnit
import AFTD.Kb.Physics.PositiveRealUnitCore
import AFTD.Kb.Physics.PositiveRealUnitCoreValNeZero
import AFTD.Kb.Physics.PositiveRealUnitCoreDivPos
import AFTD.Kb.Physics.PositiveRealUnitCoreDivNeZero
import AFTD.Kb.Physics.PositiveRealUnitCoreDivSelf
import AFTD.Kb.Physics.PositiveRealUnitCoreDivMulDivCoe
import AFTD.Kb.Physics.PositiveRealUnitCoreScaleVal
import AFTD.Kb.Physics.PositiveRealUnitCoreScaleDivSelf
import AFTD.Kb.Physics.PositiveRealUnitCoreSelfDivScale
import AFTD.Kb.Physics.PositiveRealUnitCoreScaleOne
import AFTD.Kb.Physics.PositiveRealUnitCoreScaleDivScale
import AFTD.Kb.Physics.PositiveRealUnitCoreScaleScale
import AFTD.Kb.Physics.PositiveRealUnitCoreScaleDiv

/-!
# instPositiveRealUnitCoreMassUnit

Topic: classical_mechanics   Node: 937ddd8b5d39

Provenance: formalization of a published result. Source: Physlib, `instPositiveRealUnitCoreMassUnit`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Mass/MassUnit.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

instPositiveRealUnitCoreMassUnit
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
instance instPositiveRealUnitCoreMassUnit : PositiveRealUnitCore MassUnit where
  val := MassUnit.val
  pos := MassUnit.property
  ofVal := fun r hr => ⟨r, hr⟩
  val_ofVal := by intros; rfl
  ofVal_val := by intro x; cases x; rfl
