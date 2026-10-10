import AFTD.Prelude
import AFTD.Kb.Physics.PositiveRealUnitCore
import AFTD.Kb.Physics.PositiveRealUnitCoreInstHDiv
import AFTD.Kb.Physics.PositiveRealUnitCoreValNeZero
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# PositiveRealUnitCore.div_pos

Topic: classical_mechanics   Node: da3cfd973165

Provenance: formalization of a published result. Source: Physlib, `PositiveRealUnitCore.div_pos`. Lean proof by Joseph Tooby-Smith, Hirotaka Monya, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/PositiveRealUnit.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

PositiveRealUnitCore.div_pos
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open PositiveRealUnitCore in
open NNReal in
variable {U : Type} [PositiveRealUnitCore U] in
@[simp]
lemma PositiveRealUnitCore.div_pos (x y : U) : (0 : NNReal) < x / y := by
  apply NNReal.coe_pos.mp
  change 0 < val x / val y
  exact _root_.div_pos (pos x) (pos y)
