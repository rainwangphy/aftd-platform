import AFTD.Prelude
import AFTD.Kb.Physics.PositiveRealUnitCore
import AFTD.Kb.Physics.PositiveRealUnitCoreRatio
import AFTD.Kb.Physics.PositiveRealUnitCoreValNeZero

/-!
# PositiveRealUnitCore.instHDiv

Topic: classical_mechanics   Node: 633a8472dc7a

Provenance: formalization of a published result. Source: Physlib, `PositiveRealUnitCore.instHDiv`. Lean proof by Joseph Tooby-Smith, Hirotaka Monya, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/PositiveRealUnit.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Division of two units of the same type is their nonnegative real ratio.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open PositiveRealUnitCore in
open NNReal in
variable {U : Type} [PositiveRealUnitCore U] in
/-- Division of two units of the same type is their nonnegative real ratio. -/
noncomputable instance (priority := 100) PositiveRealUnitCore.instHDiv : HDiv U U NNReal where
  hDiv := ratio
