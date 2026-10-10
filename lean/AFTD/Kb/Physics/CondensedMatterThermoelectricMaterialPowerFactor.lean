import AFTD.Prelude
import AFTD.Kb.Physics.CondensedMatterThermoelectricMaterial

/-!
# CondensedMatter.ThermoelectricMaterial.powerFactor

Topic: condensed_matter   Node: 33636b6d97ce

Provenance: formalization of a published result. Source: Physlib, `CondensedMatter.ThermoelectricMaterial.powerFactor`. Lean proof by Giuseppe Barbalinardo, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/CondensedMatter/Thermoelectric/Basic.lean (Copyright (c) 2026 Giuseppe Barbalinardo. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The thermoelectric power factor `PF = σ S²` of a material.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The thermoelectric power factor `PF = σ S²` of a material. -/
noncomputable def CondensedMatter.ThermoelectricMaterial.powerFactor (M : ThermoelectricMaterial) : ℝ := M.σ * M.S ^ 2
