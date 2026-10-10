import AFTD.Prelude
import AFTD.Kb.Physics.SuperSymmetrySU5PotentialTerm
import AFTD.Kb.Physics.SuperSymmetrySU5FieldLabel
import AFTD.Kb.Physics.SuperSymmetrySU5PotentialTermToFieldLabel
import AFTD.Kb.Physics.SuperSymmetrySU5InstFintypeFieldLabel
import AFTD.Kb.Physics.SuperSymmetrySU5PotentialTermInstDecidableInSuperPotential

/-!
# SuperSymmetry.SU5.PotentialTerm.degree

Topic: quantum_field_theory   Node: ec4d39f74b4f

Provenance: formalization of a published result. Source: Physlib, `SuperSymmetry.SU5.PotentialTerm.degree`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/SU5/Potential.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The degree of a term in the potential.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The degree of a term in the potential. -/
def SuperSymmetry.SU5.PotentialTerm.degree (T : PotentialTerm) : ℕ := T.toFieldLabel.length
