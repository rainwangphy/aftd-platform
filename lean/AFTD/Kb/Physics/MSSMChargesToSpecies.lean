import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.MSSMChargesToSMPlusH
import AFTD.Kb.Physics.MSSMChargesSplitSMPlusH
import AFTD.Kb.Physics.MSSMChargesToSpeciesMaps'
import AFTD.Kb.Physics.MSSMChargesToSplitSMPlusH
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# MSSMCharges.toSpecies

Topic: quantum_field_theory   Node: 249cca79c82f

Provenance: formalization of a published result. Source: Physlib, `MSSMCharges.toSpecies`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An equivalence between `MSSMCharges.charges` and `(Fin 6 → Fin 3 → ℚ) × (Fin 2 → ℚ))`. This splits charges up into the SM and additional fermions, and further splits the SM into species.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open BigOperators in
/-- An equivalence between `MSSMCharges.charges` and `(Fin 6 → Fin 3 → ℚ) × (Fin 2 → ℚ))`. This splits charges up into the SM and additional fermions, and further splits the SM into species. -/
@[simps!]
def MSSMCharges.toSpecies : MSSMCharges.Charges ≃ (Fin 6 → Fin 3 → ℚ) × (Fin 2 → ℚ) :=
  toSplitSMPlusH.trans (Equiv.prodCongr toSpeciesMaps' (Equiv.refl _))
