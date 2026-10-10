import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.MSSMChargesToSMPlusH
import AFTD.Kb.Physics.MSSMChargesSplitSMPlusH
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# MSSMCharges.toSplitSMPlusH

Topic: quantum_field_theory   Node: cf0d35c92a0c

Provenance: formalization of a published result. Source: Physlib, `MSSMCharges.toSplitSMPlusH`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An equivalence between `MSSMCharges.charges` and `(Fin 18 → ℚ) × (Fin 2 → ℚ)`. This splits the charges up into the SM and the additional ones for the MSSM.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open BigOperators in
/-- An equivalence between `MSSMCharges.charges` and `(Fin 18 → ℚ) × (Fin 2 → ℚ)`. This splits the charges up into the SM and the additional ones for the MSSM. -/
@[simps!]
def MSSMCharges.toSplitSMPlusH : MSSMCharges.Charges ≃ (Fin 18 → ℚ) × (Fin 2 → ℚ) :=
  toSMPlusH.trans splitSMPlusH
