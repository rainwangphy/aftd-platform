import AFTD.Prelude
import AFTD.Kb.Physics.PositiveRealUnitCore

/-!
# PositiveRealUnitCore.instInhabited

Topic: classical_mechanics   Node: 33585cd8bc3a

Provenance: formalization of a published result. Source: Physlib, `PositiveRealUnitCore.instInhabited`. Lean proof by Joseph Tooby-Smith, Hirotaka Monya, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/PositiveRealUnit.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The unit of magnitude one supplies a default unit.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
variable {U : Type} [PositiveRealUnitCore U] in
/-- The unit of magnitude one supplies a default unit. -/
instance (priority := 100) PositiveRealUnitCore.instInhabited : Inhabited U where
  default := ofVal 1 (by norm_num)
