import AFTD.Prelude
import AFTD.Kb.Physics.CondensedMatterThermoelectricMaterial
import AFTD.Kb.Physics.CondensedMatterThermoelectricMaterialFigureOfMerit
import AFTD.Kb.Physics.CondensedMatterThermoelectricMaterialPowerFactor
import AFTD.Kb.Physics.CondensedMatterThermoelectricMaterialTotalThermalConductivity

/-!
# CondensedMatter.ThermoelectricMaterial.figureOfMerit_le_of_le

Topic: condensed_matter   Node: 93dbdacff7cc

Provenance: formalization of a published result. Source: Physlib, `CondensedMatter.ThermoelectricMaterial.figureOfMerit_le_of_le`. Lean proof by Giuseppe Barbalinardo, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/CondensedMatter/Thermoelectric/Basic.lean (Copyright (c) 2026 Giuseppe Barbalinardo. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lowering the lattice thermal conductivity raises the figure of merit: if `M.κl ≤ κl'` then the material with lattice conductivity `κl'` (all other coefficients equal) has the smaller `zT`. This is the phonon-glass electron-crystal design principle: scatter phonons without degrading electronic transport. Note the hypotheses: no condition on the Seebeck coefficient is needed, since monotonicity only requires the numerator `σ S² T` to be nonnegative.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Lowering the lattice thermal conductivity raises the figure of merit: if `M.κl ≤ κl'` then the material with lattice conductivity `κl'` (all other coefficients equal) has the smaller `zT`. This is the phonon-glass electron-crystal design principle: scatter phonons without degrading electronic transport. Note the hypotheses: no condition on the Seebeck coefficient is needed, since monotonicity only requires the numerator `σ S² T` to be nonnegative. -/
lemma CondensedMatter.ThermoelectricMaterial.figureOfMerit_le_of_le (M : ThermoelectricMaterial) {κl' T : ℝ}
    (hpos : 0 < κl') (h : M.κl ≤ κl') (hT : 0 ≤ T) :
    figureOfMerit { M with κl := κl', κl_pos := hpos } T ≤ M.figureOfMerit T := by
  unfold figureOfMerit powerFactor totalThermalConductivity
  have hnum : (0 : ℝ) ≤ M.σ * M.S ^ 2 * T := by
    have hσ := M.σ_pos
    positivity
  have hden : 0 < M.κl + M.κe := add_pos_of_pos_of_nonneg M.κl_pos M.κe_nonneg
  gcongr
