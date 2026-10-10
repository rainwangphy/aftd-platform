import AFTD.Prelude
import AFTD.Kb.Physics.PositiveRealUnitCore
import AFTD.Kb.Physics.PositiveRealUnitCoreInstHDiv
import AFTD.Kb.Physics.PositiveRealUnitCoreValNeZero

/-!
# PositiveRealUnitCore.div_eq_val

Topic: classical_mechanics   Node: 9e95665723de

Provenance: formalization of a published result. Source: Physlib, `PositiveRealUnitCore.div_eq_val`. Lean proof by Joseph Tooby-Smith, Hirotaka Monya, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/PositiveRealUnit.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Unit division agrees with the ratio of the two magnitudes.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open PositiveRealUnitCore in
open NNReal in
variable {U : Type} [PositiveRealUnitCore U] in
/-- Unit division agrees with the ratio of the two magnitudes. -/
lemma PositiveRealUnitCore.div_eq_val (x y : U) :
    x / y = (⟨val x / val y, _root_.div_nonneg (pos x).le (pos y).le⟩ : NNReal) := rfl
