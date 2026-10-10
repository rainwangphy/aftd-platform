import AFTD.Prelude
import AFTD.Kb.Physics.SuperSymmetrySU5FieldLabel

/-!
# SuperSymmetry.SU5.instFintypeFieldLabel

Topic: quantum_field_theory   Node: a5eef4ee8721

Provenance: formalization of a published result. Source: Physlib, `SuperSymmetry.SU5.instFintypeFieldLabel`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/SU5/FieldLabels.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SuperSymmetry.SU5.instFintypeFieldLabel
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance SuperSymmetry.SU5.instFintypeFieldLabel : Fintype FieldLabel where
  elems := {.fiveBarHu, .fiveHu, .fiveBarHd, .fiveHd, .fiveBarMatter, .fiveMatter, .tenMatter}
  complete := fun x => by cases x <;> decide
