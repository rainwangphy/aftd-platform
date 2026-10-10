import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.MSSMSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.MSSMChargesToSMSpecies
import AFTD.Kb.Physics.MSSMChargesHd
import AFTD.Kb.Physics.MSSMChargesHu
import AFTD.Kb.Physics.MSSMChargesToSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstNonemptyStrategyFinOfNatNatToStrategicGame

/-!
# MSSMCharges.charges_eq_toSpecies_eq

Topic: quantum_field_theory   Node: 68aeab00365c

Provenance: formalization of a published result. Source: Physlib, `MSSMCharges.charges_eq_toSpecies_eq`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

MSSMCharges.charges_eq_toSpecies_eq
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open BigOperators in
lemma MSSMCharges.charges_eq_toSpecies_eq (S T : MSSMCharges.Charges) :
    S = T ↔ (∀ i, toSMSpecies i S = toSMSpecies i T) ∧ Hd S = Hd T ∧ Hu S = Hu T := by
  refine ⟨fun h => h ▸ ⟨fun _ => rfl, rfl, rfl⟩, fun h => toSpecies.injective ?_⟩
  exact Prod.ext (funext h.1) (funext fun | 0 => h.2.1 | 1 => h.2.2)
