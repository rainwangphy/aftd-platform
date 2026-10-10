import AFTD.Prelude
import AFTD.Kb.Physics.CondensedMatterThermoelectricMaterial

/-!
# CondensedMatter.ThermoelectricMaterial.totalThermalConductivity

Topic: condensed_matter   Node: 97b0b4dd77ed

Provenance: formalization of a published result. Source: Physlib, `CondensedMatter.ThermoelectricMaterial.totalThermalConductivity`. Lean proof by Giuseppe Barbalinardo, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/CondensedMatter/Thermoelectric/Basic.lean (Copyright (c) 2026 Giuseppe Barbalinardo. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The total thermal conductivity `κl + κe` of a material, the sum of the lattice (phonon) and electronic contributions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The total thermal conductivity `κl + κe` of a material, the sum of the lattice (phonon) and electronic contributions. -/
noncomputable def CondensedMatter.ThermoelectricMaterial.totalThermalConductivity (M : ThermoelectricMaterial) : ℝ := M.κl + M.κe
