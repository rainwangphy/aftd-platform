import AFTD.Prelude

/-!
# TemperatureUnit

Topic: statistical_mechanics   Node: a55cc90f6312

Provenance: formalization of a published result. Source: Physlib, `TemperatureUnit`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Thermodynamics/Temperature/TemperatureUnits.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The choices of translationally-invariant metrics on the temperature-manifold. Such a choice corresponds to a choice of units for temperature.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
/-- The choices of translationally-invariant metrics on the temperature-manifold. Such a choice corresponds to a choice of units for temperature. -/
structure TemperatureUnit where
  /-- The underlying scale of the unit. -/
  val : ℝ
  property : 0 < val
