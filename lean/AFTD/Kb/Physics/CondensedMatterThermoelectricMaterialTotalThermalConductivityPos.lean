import AFTD.Prelude
import AFTD.Kb.Physics.CondensedMatterThermoelectricMaterial
import AFTD.Kb.Physics.CondensedMatterThermoelectricMaterialTotalThermalConductivity

/-!
# CondensedMatter.ThermoelectricMaterial.totalThermalConductivity_pos

Topic: condensed_matter   Node: fa956ed68189

Provenance: formalization of a published result. Source: Physlib, `CondensedMatter.ThermoelectricMaterial.totalThermalConductivity_pos`. Lean proof by Giuseppe Barbalinardo, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/CondensedMatter/Thermoelectric/Basic.lean (Copyright (c) 2026 Giuseppe Barbalinardo. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The total thermal conductivity is positive.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The total thermal conductivity is positive. -/
lemma CondensedMatter.ThermoelectricMaterial.totalThermalConductivity_pos (M : ThermoelectricMaterial) :
    0 < M.totalThermalConductivity :=
  add_pos_of_pos_of_nonneg M.κl_pos M.κe_nonneg
