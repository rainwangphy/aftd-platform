import AFTD.Prelude
import AFTD.Kb.Physics.Temperature
import AFTD.Kb.Physics.TemperatureInstCoeNNReal
import AFTD.Kb.Physics.TemperatureInstCoeReal
import AFTD.Kb.Physics.TemperatureInstTopologicalSpace

/-!
# Temperature.instZero

Topic: statistical_mechanics   Node: c9e63cfa6c97

Provenance: formalization of a published result. Source: Physlib, `Temperature.instZero`. Lean proof by Matteo Cipollina, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Thermodynamics/Temperature/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Temperature.instZero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
instance Temperature.instZero : Zero Temperature := ⟨⟨0⟩⟩
