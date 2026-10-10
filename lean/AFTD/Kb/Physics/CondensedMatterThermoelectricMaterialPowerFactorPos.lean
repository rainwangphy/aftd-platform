import AFTD.Prelude
import AFTD.Kb.Physics.CondensedMatterThermoelectricMaterial
import AFTD.Kb.Physics.CondensedMatterThermoelectricMaterialPowerFactor

/-!
# CondensedMatter.ThermoelectricMaterial.powerFactor_pos

Topic: condensed_matter   Node: 16a29eced969

Provenance: formalization of a published result. Source: Physlib, `CondensedMatter.ThermoelectricMaterial.powerFactor_pos`. Lean proof by Giuseppe Barbalinardo, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/CondensedMatter/Thermoelectric/Basic.lean (Copyright (c) 2026 Giuseppe Barbalinardo. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The power factor is positive when the Seebeck coefficient is nonzero.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The power factor is positive when the Seebeck coefficient is nonzero. -/
lemma CondensedMatter.ThermoelectricMaterial.powerFactor_pos {M : ThermoelectricMaterial} (hS : M.S ≠ 0) :
    0 < M.powerFactor := by
  unfold powerFactor
  -- `positivity` does not look through the projection, so name the field.
  have hσ := M.σ_pos
  positivity
