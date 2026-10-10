import AFTD.Prelude
import AFTD.Kb.Physics.Temperature
import AFTD.Kb.Physics.TemperatureOfBeta
import AFTD.Kb.Physics.TemperatureBeta
import AFTD.Kb.Physics.TemperatureExt
import AFTD.Kb.Physics.ConstantsKB
import AFTD.Kb.Physics.TemperatureToReal
import AFTD.Kb.Physics.ConstantsKBNeZero
import AFTD.Kb.Physics.TemperatureBetaOfBeta
import AFTD.Kb.Physics.TemperatureInstCoeNNReal
import AFTD.Kb.Physics.TemperatureInstCoeReal
import AFTD.Kb.Physics.TemperatureInstTopologicalSpace
import AFTD.Kb.Physics.TemperatureInstZero

/-!
# Temperature.ofβ_β

Topic: statistical_mechanics   Node: 4c38036b74a1

Provenance: formalization of a published result. Source: Physlib, `Temperature.ofβ_β`. Lean proof by Matteo Cipollina, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Thermodynamics/Temperature/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Temperature.ofβ_β
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
open Constants in
@[simp]
lemma Temperature.ofβ_β (T : Temperature) : ofβ (β T) = T := by
  apply Temperature.ext
  apply NNReal.coe_injective
  show 1 / (kB * (1 / (kB * (T : ℝ)))) = (T : ℝ)
  rw [mul_one_div, one_div_div, mul_div_cancel_left₀ _ kB_ne_zero]
