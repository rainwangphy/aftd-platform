import AFTD.Prelude
import AFTD.Kb.Physics.SuperSymmetrySU5PotentialTerm
import AFTD.Kb.Physics.SuperSymmetrySU5PotentialTermDegree
import AFTD.Kb.Physics.SuperSymmetrySU5InstFintypeFieldLabel
import AFTD.Kb.Physics.SuperSymmetrySU5PotentialTermInstDecidableInSuperPotential

/-!
# SuperSymmetry.SU5.PotentialTerm.degree_le_four

Topic: quantum_field_theory   Node: 2817c82cec41

Provenance: formalization of a published result. Source: Physlib, `SuperSymmetry.SU5.PotentialTerm.degree_le_four`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/SU5/Potential.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SuperSymmetry.SU5.PotentialTerm.degree_le_four
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
lemma SuperSymmetry.SU5.PotentialTerm.degree_le_four (T : PotentialTerm) : T.degree ≤ 4 := by
  revert T
  decide
