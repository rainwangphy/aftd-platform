import AFTD.Prelude
import AFTD.Kb.Physics.LengthUnit
import AFTD.Kb.Physics.TimeUnit
import AFTD.Kb.Physics.MassUnit
import AFTD.Kb.Physics.ChargeUnit
import AFTD.Kb.Physics.TemperatureUnit
import AFTD.Kb.Physics.InstPositiveRealUnitCoreTimeUnit
import AFTD.Kb.Physics.InstPositiveRealUnitCoreLengthUnit
import AFTD.Kb.Physics.InstPositiveRealUnitCoreMassUnit
import AFTD.Kb.Physics.InstPositiveRealUnitCoreChargeUnit
import AFTD.Kb.Physics.InstPositiveRealUnitCoreTemperatureUnit

/-!
# LTMCTUnitChoices

Topic: classical_mechanics   Node: e00736dc5601

Provenance: formalization of a published result. Source: Physlib, `LTMCTUnitChoices`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The choice of units.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
/-- The choice of units. -/
@[ext]
structure LTMCTUnitChoices where
  /-- The length unit. -/
  length : LengthUnit
  /-- The time unit. -/
  time : TimeUnit
  /-- The mass unit. -/
  mass : MassUnit
  /-- The charge unit. -/
  charge : ChargeUnit
  /-- The temperature unit. -/
  temperature : TemperatureUnit
