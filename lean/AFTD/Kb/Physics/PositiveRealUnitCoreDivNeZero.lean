import AFTD.Prelude
import AFTD.Kb.Physics.PositiveRealUnitCore
import AFTD.Kb.Physics.PositiveRealUnitCoreInstHDiv
import AFTD.Kb.Physics.PositiveRealUnitCoreDivPos
import AFTD.Kb.Physics.PositiveRealUnitCoreValNeZero
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# PositiveRealUnitCore.div_ne_zero

Topic: classical_mechanics   Node: d53cb65d2727

Provenance: formalization of a published result. Source: Physlib, `PositiveRealUnitCore.div_ne_zero`. Lean proof by Joseph Tooby-Smith, Hirotaka Monya, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/PositiveRealUnit.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

PositiveRealUnitCore.div_ne_zero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open PositiveRealUnitCore in
open NNReal in
variable {U : Type} [PositiveRealUnitCore U] in
@[simp]
lemma PositiveRealUnitCore.div_ne_zero (x y : U) : x / y ≠ (0 : NNReal) :=
  ne_of_gt (div_pos x y)
