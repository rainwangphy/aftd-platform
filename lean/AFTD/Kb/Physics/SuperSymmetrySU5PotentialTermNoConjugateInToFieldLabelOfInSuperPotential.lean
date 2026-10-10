import AFTD.Prelude
import AFTD.Kb.Physics.SuperSymmetrySU5PotentialTerm
import AFTD.Kb.Physics.SuperSymmetrySU5PotentialTermInSuperPotential
import AFTD.Kb.Physics.SuperSymmetrySU5FieldLabel
import AFTD.Kb.Physics.SuperSymmetrySU5PotentialTermToFieldLabel
import AFTD.Kb.Physics.SuperSymmetrySU5PotentialTermInstDecidableInSuperPotential
import AFTD.Kb.Physics.SuperSymmetrySU5InstFintypeFieldLabel

/-!
# SuperSymmetry.SU5.PotentialTerm.no_conjugate_in_toFieldLabel_of_inSuperPotential

Topic: quantum_field_theory   Node: 3c78e704282c

Provenance: formalization of a published result. Source: Physlib, `SuperSymmetry.SU5.PotentialTerm.no_conjugate_in_toFieldLabel_of_inSuperPotential`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/SU5/Potential.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 adapted; compiled here.

The terms within the super-potential contain no conjugate fields.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The terms within the super-potential contain no conjugate fields. -/
lemma SuperSymmetry.SU5.PotentialTerm.no_conjugate_in_toFieldLabel_of_inSuperPotential {T : PotentialTerm}
    (h : T.InSuperPotential) : FieldLabel.fiveMatter ∉ T.toFieldLabel ∧
    FieldLabel.fiveHd ∉ T.toFieldLabel ∧ FieldLabel.fiveBarHu ∉ T.toFieldLabel := by
  revert T
  decide
