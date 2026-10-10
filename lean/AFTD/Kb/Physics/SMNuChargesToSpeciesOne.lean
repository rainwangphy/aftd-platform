import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMNuCharges
import AFTD.Kb.Physics.SMNuSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMNuChargesToSpecies
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# SMνCharges.toSpecies_one

Topic: quantum_field_theory   Node: ea7eaf9b6c3f

Provenance: formalization of a published result. Source: Physlib, `SMνCharges.toSpecies_one`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SMνCharges.toSpecies_one
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMνCharges in
open Nat in
open BigOperators in
variable {n : ℕ} in
lemma SMνCharges.toSpecies_one (S : (SMνCharges 1).Charges) (j : Fin 6) :
    toSpecies j S ⟨0, zero_lt_succ 0⟩ = S j := by
  match j with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
