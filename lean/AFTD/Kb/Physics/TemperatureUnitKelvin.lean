import AFTD.Prelude
import AFTD.Kb.Physics.TemperatureUnit
import AFTD.Kb.Physics.InstPositiveRealUnitCoreTemperatureUnit

/-!
# TemperatureUnit.kelvin

Topic: statistical_mechanics   Node: 2be0c5d5c4d7

Provenance: formalization of a published result. Source: Physlib, `TemperatureUnit.kelvin`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Thermodynamics/Temperature/TemperatureUnits.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The definition of a temperature unit of kelvin.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
open NNReal in
/-- The definition of a temperature unit of kelvin. -/
def TemperatureUnit.kelvin : TemperatureUnit := ⟨1, by norm_num⟩
