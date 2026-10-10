import AFTD.Prelude
import AFTD.Kb.Physics.SuperSymmetrySU5PotentialTerm
import AFTD.Kb.Physics.SuperSymmetrySU5PotentialTermToFieldLabel
import AFTD.Kb.Physics.SuperSymmetrySU5InstFintypeFieldLabel

/-!
# SuperSymmetry.SU5.PotentialTerm.InSuperPotential

Topic: quantum_field_theory   Node: 28e43aa408ab

Provenance: formalization of a published result. Source: Physlib, `SuperSymmetry.SU5.PotentialTerm.InSuperPotential`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/SU5/Potential.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The proposition which is true on those terms which are members of the super potential.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The proposition which is true on those terms which are members of the super potential. -/
def SuperSymmetry.SU5.PotentialTerm.InSuperPotential : PotentialTerm → Prop
  | μ => True
  | β => True
  | Λ => True
  | W1 => True
  | W2 => True
  | W3 => True
  | W4 => True
  | K1 => False
  | K2 => False
  | topYukawa => True
  | bottomYukawa => True
