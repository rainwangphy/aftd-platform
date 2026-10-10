import AFTD.Prelude

/-!
# CondensedMatter.ThermoelectricMaterial

Topic: condensed_matter   Node: 6e892c49d9c6

Provenance: formalization of a published result. Source: Physlib, `CondensedMatter.ThermoelectricMaterial`. Lean proof by Giuseppe Barbalinardo, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/CondensedMatter/Thermoelectric/Basic.lean (Copyright (c) 2026 Giuseppe Barbalinardo. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A thermoelectric material in the linear-response regime, characterized by its four transport coefficients.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A thermoelectric material in the linear-response regime, characterized by its four transport coefficients. -/
structure CondensedMatter.ThermoelectricMaterial where
  /-- The Seebeck coefficient `S`: the voltage developed per unit temperature
  difference. Its sign records the dominant carrier type. -/
  S : ℝ
  /-- The electrical conductivity `σ`. -/
  σ : ℝ
  /-- The lattice (phonon) contribution `κl` to the thermal conductivity. -/
  κl : ℝ
  /-- The electronic contribution `κe` to the thermal conductivity. -/
  κe : ℝ
  σ_pos : 0 < σ
  κl_pos : 0 < κl
  κe_nonneg : 0 ≤ κe
