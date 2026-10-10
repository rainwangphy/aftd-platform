import AFTD.Prelude
import AFTD.Kb.Physics.SuperSymmetrySU5PotentialTermInSuperPotential
import AFTD.Kb.Physics.SuperSymmetrySU5PotentialTerm
import AFTD.Kb.Physics.SuperSymmetrySU5PotentialTermToFieldLabel
import AFTD.Kb.Physics.SuperSymmetrySU5InstFintypeFieldLabel

/-!
# SuperSymmetry.SU5.PotentialTerm.instDecidableInSuperPotential

Topic: quantum_field_theory   Node: 32613cc9f027

Provenance: formalization of a published result. Source: Physlib, `SuperSymmetry.SU5.PotentialTerm.instDecidableInSuperPotential`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/SU5/Potential.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SuperSymmetry.SU5.PotentialTerm.instDecidableInSuperPotential
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance SuperSymmetry.SU5.PotentialTerm.instDecidableInSuperPotential : (T : PotentialTerm) → Decidable (InSuperPotential T)
  | μ => inferInstanceAs (Decidable True)
  | β => inferInstanceAs (Decidable True)
  | Λ => inferInstanceAs (Decidable True)
  | W1 => inferInstanceAs (Decidable True)
  | W2 => inferInstanceAs (Decidable True)
  | W3 => inferInstanceAs (Decidable True)
  | W4 => inferInstanceAs (Decidable True)
  | K1 => inferInstanceAs (Decidable False)
  | K2 => inferInstanceAs (Decidable False)
  | topYukawa => inferInstanceAs (Decidable True)
  | bottomYukawa => inferInstanceAs (Decidable True)
