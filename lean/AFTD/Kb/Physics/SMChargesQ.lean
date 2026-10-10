import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMCharges
import AFTD.Kb.Physics.SMSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMChargesToSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# SMCharges.Q

Topic: quantum_field_theory   Node: e6f250f81a30

Provenance: formalization of a published result. Source: Physlib, `SMCharges.Q`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The `Q` charges as a map `Fin n → ℚ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMCharges in
open Nat in
open BigOperators in
variable {n : ℕ} in
/-- The `Q` charges as a map `Fin n → ℚ`. -/
abbrev SMCharges.Q := @toSpecies n 0
