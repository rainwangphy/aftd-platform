import AFTD.Prelude
import AFTD.Kb.Physics.PositiveRealUnitCore
import AFTD.Kb.Physics.PositiveRealUnitCoreInstHDiv
import AFTD.Kb.Physics.PositiveRealUnitCoreValNeZero
import AFTD.Kb.Physics.PositiveRealUnitCoreDivPos
import AFTD.Kb.Physics.PositiveRealUnitCoreDivNeZero

/-!
# PositiveRealUnitCore.div_self

Topic: classical_mechanics   Node: 3133ef219b7a

Provenance: formalization of a published result. Source: Physlib, `PositiveRealUnitCore.div_self`. Lean proof by Joseph Tooby-Smith, Hirotaka Monya, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/PositiveRealUnit.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

PositiveRealUnitCore.div_self
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open PositiveRealUnitCore in
open NNReal in
variable {U : Type} [PositiveRealUnitCore U] in
@[simp]
lemma PositiveRealUnitCore.div_self (x : U) : x / x = (1 : NNReal) := by
  apply NNReal.eq
  change val x / val x = 1
  exact _root_.div_self (val_ne_zero x)
