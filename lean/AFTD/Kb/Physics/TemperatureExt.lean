import AFTD.Prelude
import AFTD.Kb.Physics.Temperature
import AFTD.Kb.Physics.TemperatureInstCoeNNReal
import AFTD.Kb.Physics.TemperatureInstCoeReal
import AFTD.Kb.Physics.TemperatureInstTopologicalSpace
import AFTD.Kb.Physics.TemperatureInstZero

/-!
# Temperature.ext

Topic: statistical_mechanics   Node: c2d3e10dc54d

Provenance: formalization of a published result. Source: Physlib, `Temperature.ext`. Lean proof by Matteo Cipollina, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Thermodynamics/Temperature/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Temperature.ext
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
@[ext] lemma Temperature.ext {T₁ T₂ : Temperature} (h : T₁.val = T₂.val) : T₁ = T₂ := by
  cases T₁; cases T₂; cases h; rfl
