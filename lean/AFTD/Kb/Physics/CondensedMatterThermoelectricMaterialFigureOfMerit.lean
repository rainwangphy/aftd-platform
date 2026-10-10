import AFTD.Prelude
import AFTD.Kb.Physics.CondensedMatterThermoelectricMaterial
import AFTD.Kb.Physics.CondensedMatterThermoelectricMaterialPowerFactor
import AFTD.Kb.Physics.CondensedMatterThermoelectricMaterialTotalThermalConductivity

/-!
# CondensedMatter.ThermoelectricMaterial.figureOfMerit

Topic: condensed_matter   Node: ae27865c5d1d

Provenance: formalization of a published result. Source: Physlib, `CondensedMatter.ThermoelectricMaterial.figureOfMerit`. Lean proof by Giuseppe Barbalinardo, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/CondensedMatter/Thermoelectric/Basic.lean (Copyright (c) 2026 Giuseppe Barbalinardo. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The dimensionless thermoelectric figure of merit `zT = PF · T / (κl + κe)` of a material at absolute temperature `T`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The dimensionless thermoelectric figure of merit `zT = PF · T / (κl + κe)` of a material at absolute temperature `T`. -/
noncomputable def CondensedMatter.ThermoelectricMaterial.figureOfMerit (M : ThermoelectricMaterial) (T : ℝ) : ℝ :=
  M.powerFactor * T / M.totalThermalConductivity
