import AFTD.Prelude
import AFTD.Kb.Physics.CondensedMatterThermoelectricMaterial
import AFTD.Kb.Physics.CondensedMatterThermoelectricMaterialFigureOfMerit
import AFTD.Kb.Physics.CondensedMatterThermoelectricMaterialPowerFactor
import AFTD.Kb.Physics.CondensedMatterThermoelectricMaterialTotalThermalConductivity

/-!
# CondensedMatter.ThermoelectricMaterial.figureOfMerit_eq

Topic: condensed_matter   Node: 2c78e45acf0d

Provenance: formalization of a published result. Source: Physlib, `CondensedMatter.ThermoelectricMaterial.figureOfMerit_eq`. Lean proof by Giuseppe Barbalinardo, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/CondensedMatter/Thermoelectric/Basic.lean (Copyright (c) 2026 Giuseppe Barbalinardo. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The figure of merit in its standard flat form `zT = σ S² T / (κl + κe)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The figure of merit in its standard flat form `zT = σ S² T / (κl + κe)`. -/
lemma CondensedMatter.ThermoelectricMaterial.figureOfMerit_eq (M : ThermoelectricMaterial) (T : ℝ) :
    M.figureOfMerit T = M.σ * M.S ^ 2 * T / (M.κl + M.κe) := by
  unfold figureOfMerit powerFactor totalThermalConductivity
  ring
