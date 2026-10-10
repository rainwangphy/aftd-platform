import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMNuCharges
import AFTD.Kb.Physics.SMNuSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMNuChargesToSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.GameTheoryEconomics.LxvVal

/-!
# SMνCharges.Q

Topic: quantum_field_theory   Node: 9b1e9da9bcc9

Provenance: formalization of a published result. Source: Physlib, `SMνCharges.Q`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The `Q` charges as a map `Fin n → ℚ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMνCharges in
open Nat in
open BigOperators in
variable {n : ℕ} in
/-- The `Q` charges as a map `Fin n → ℚ`. -/
abbrev SMνCharges.Q := @toSpecies n 0
