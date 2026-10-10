import AFTD.Prelude
import AFTD.Kb.Physics.SuperSymmetrySU5FieldLabel
import AFTD.Kb.Physics.SuperSymmetrySU5PotentialTerm
import AFTD.Kb.Physics.SuperSymmetrySU5InstFintypeFieldLabel

/-!
# SuperSymmetry.SU5.PotentialTerm.toFieldLabel

Topic: quantum_field_theory   Node: 4d342a63d64e

Provenance: formalization of a published result. Source: Physlib, `SuperSymmetry.SU5.PotentialTerm.toFieldLabel`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/SU5/Potential.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The fields contained within a given term of the potential.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The fields contained within a given term of the potential. -/
def SuperSymmetry.SU5.PotentialTerm.toFieldLabel : PotentialTerm → List FieldLabel
  | μ => [.fiveBarHd, .fiveHu]
  | β => [.fiveHu, .fiveBarMatter]
  | Λ => [.fiveBarMatter, .fiveBarMatter, .tenMatter]
  | W1 => [.tenMatter, .tenMatter, .tenMatter, .fiveBarMatter]
  | W2 => [.tenMatter, .tenMatter, .tenMatter, .fiveBarHd]
  | W3 => [.fiveBarMatter, .fiveBarMatter, .fiveHu, .fiveHu]
  | W4 => [.fiveBarMatter, .fiveBarHd, .fiveHu, .fiveHu]
  | K1 => [.tenMatter, .tenMatter, .fiveMatter]
  | K2 => [.fiveBarHu, .fiveBarHd, .tenMatter]
  | topYukawa => [.tenMatter, .tenMatter, .fiveHu]
  | bottomYukawa => [.tenMatter, .fiveBarMatter, .fiveBarHd]
