import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# MSSMCharges.toSMPlusH

Topic: quantum_field_theory   Node: 85ff00827883

Provenance: formalization of a published result. Source: Physlib, `MSSMCharges.toSMPlusH`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An equivalence between `MSSMCharges.charges` and the space of maps `(Fin 18 ⊕ Fin 2 → ℚ)`. The first 18 factors corresponds to the SM fermions, while the last two are the higgsions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open BigOperators in
/-- An equivalence between `MSSMCharges.charges` and the space of maps `(Fin 18 ⊕ Fin 2 → ℚ)`. The first 18 factors corresponds to the SM fermions, while the last two are the higgsions. -/
@[simps!]
def MSSMCharges.toSMPlusH : MSSMCharges.Charges ≃ (Fin 18 ⊕ Fin 2 → ℚ) :=
  ((@finSumFinEquiv 18 2).arrowCongr (Equiv.refl ℚ)).symm
