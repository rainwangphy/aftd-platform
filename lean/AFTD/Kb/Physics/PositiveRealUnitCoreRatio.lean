import AFTD.Prelude
import AFTD.Kb.Physics.PositiveRealUnitCore
import AFTD.Kb.Physics.PositiveRealUnitCoreValNeZero

/-!
# PositiveRealUnitCore.ratio

Topic: classical_mechanics   Node: b9f43532bcd3

Provenance: formalization of a published result. Source: Physlib, `PositiveRealUnitCore.ratio`. Lean proof by Joseph Tooby-Smith, Hirotaka Monya, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/PositiveRealUnit.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The ratio of the magnitudes of two units of the same type.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
variable {U : Type} [PositiveRealUnitCore U] in
/-- The ratio of the magnitudes of two units of the same type. -/
noncomputable def PositiveRealUnitCore.ratio (x y : U) : NNReal :=
  ⟨val x / val y, _root_.div_nonneg (pos x).le (pos y).le⟩
