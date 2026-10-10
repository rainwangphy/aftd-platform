import AFTD.Prelude
import AFTD.Kb.Physics.SuperSymmetrySU5PotentialTerm
import AFTD.Kb.Physics.SuperSymmetrySU5PotentialTermRParity
import AFTD.Kb.Physics.SuperSymmetrySU5InstFintypeFieldLabel
import AFTD.Kb.Physics.SuperSymmetrySU5PotentialTermInstDecidableInSuperPotential

/-!
# SuperSymmetry.SU5.PotentialTerm.violates_RParity_iff_mem

Topic: quantum_field_theory   Node: c0ac6c8101af

Provenance: formalization of a published result. Source: Physlib, `SuperSymmetry.SU5.PotentialTerm.violates_RParity_iff_mem`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/SU5/Potential.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SuperSymmetry.SU5.PotentialTerm.violates_RParity_iff_mem
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
lemma SuperSymmetry.SU5.PotentialTerm.violates_RParity_iff_mem {T : PotentialTerm} :
    T.RParity = 1 ↔ T ∈ ({β, Λ, W2, W4, K1, K2} : Finset PotentialTerm) := by
  revert T
  decide
