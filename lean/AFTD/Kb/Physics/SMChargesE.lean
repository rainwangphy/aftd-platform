import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMCharges
import AFTD.Kb.Physics.SMSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMChargesToSpecies
import AFTD.Kb.Physics.SMChargesQ
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# SMCharges.E

Topic: quantum_field_theory   Node: e54b25731868

Provenance: formalization of a published result. Source: Physlib, `SMCharges.E`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The `E` charges as a map `Fin n → ℚ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMCharges in
open Nat in
open BigOperators in
variable {n : ℕ} in
/-- The `E` charges as a map `Fin n → ℚ`. -/
abbrev SMCharges.E := @toSpecies n 4
