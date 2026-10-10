import AFTD.Prelude
import AFTD.Kb.Physics.PositiveRealUnitCore

/-!
# PositiveRealUnitCore.val_ne_zero

Topic: classical_mechanics   Node: 6a4a554ace5d

Provenance: formalization of a published result. Source: Physlib, `PositiveRealUnitCore.val_ne_zero`. Lean proof by Joseph Tooby-Smith, Hirotaka Monya, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/PositiveRealUnit.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

PositiveRealUnitCore.val_ne_zero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
variable {U : Type} [PositiveRealUnitCore U] in
@[simp]
lemma PositiveRealUnitCore.val_ne_zero (x : U) : val x ≠ 0 :=
  ne_of_gt (pos x)
