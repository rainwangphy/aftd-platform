import AFTD.Prelude
import AFTD.Kb.Physics.Temperature
import AFTD.Kb.Physics.ConstantsKB
import AFTD.Kb.Physics.TemperatureToReal
import AFTD.Kb.Physics.ConstantsKBNonneg
import AFTD.Kb.Physics.TemperatureInstCoeNNReal
import AFTD.Kb.Physics.TemperatureInstCoeReal
import AFTD.Kb.Physics.TemperatureInstTopologicalSpace
import AFTD.Kb.Physics.TemperatureInstZero

/-!
# Temperature.β

Topic: statistical_mechanics   Node: ade5b9a1e385

Provenance: formalization of a published result. Source: Physlib, `Temperature.β`. Lean proof by Matteo Cipollina, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Thermodynamics/Temperature/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The inverse temperature defined as `1/(kB * T)` in a given, but arbitrary set of units. This has dimensions equivalent to `Energy`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
open Constants in
/-- The inverse temperature defined as `1/(kB * T)` in a given, but arbitrary set of units. This has dimensions equivalent to `Energy`. -/
noncomputable def Temperature.β (T : Temperature) : ℝ≥0 :=
  ⟨1 / (kB * (T : ℝ)), div_nonneg zero_le_one (mul_nonneg kB_nonneg T.val.2)⟩
