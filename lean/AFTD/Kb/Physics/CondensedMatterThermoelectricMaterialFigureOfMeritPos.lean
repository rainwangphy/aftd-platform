import AFTD.Prelude
import AFTD.Kb.Physics.CondensedMatterThermoelectricMaterial
import AFTD.Kb.Physics.CondensedMatterThermoelectricMaterialFigureOfMerit
import AFTD.Kb.Physics.CondensedMatterThermoelectricMaterialPowerFactor
import AFTD.Kb.Physics.CondensedMatterThermoelectricMaterialTotalThermalConductivity
import AFTD.Kb.Physics.CondensedMatterThermoelectricMaterialPowerFactorPos
import AFTD.Kb.Physics.CondensedMatterThermoelectricMaterialTotalThermalConductivityPos

/-!
# CondensedMatter.ThermoelectricMaterial.figureOfMerit_pos

Topic: condensed_matter   Node: 7c66b968e599

Provenance: formalization of a published result. Source: Physlib, `CondensedMatter.ThermoelectricMaterial.figureOfMerit_pos`. Lean proof by Giuseppe Barbalinardo, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/CondensedMatter/Thermoelectric/Basic.lean (Copyright (c) 2026 Giuseppe Barbalinardo. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The figure of merit is positive at positive temperature when the Seebeck coefficient is nonzero.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The figure of merit is positive at positive temperature when the Seebeck coefficient is nonzero. -/
lemma CondensedMatter.ThermoelectricMaterial.figureOfMerit_pos {M : ThermoelectricMaterial} {T : ℝ}
    (hS : M.S ≠ 0) (hT : 0 < T) :
    0 < M.figureOfMerit T :=
  div_pos (mul_pos (powerFactor_pos hS) hT) M.totalThermalConductivity_pos
