import AFTD.Prelude
import AFTD.Kb.Physics.Temperature
import AFTD.Kb.Physics.TemperatureToReal
import AFTD.Kb.Physics.TemperatureInstCoeNNReal

/-!
# Temperature.instCoeReal

Topic: statistical_mechanics   Node: 08fca0abb272

Provenance: formalization of a published result. Source: Physlib, `Temperature.instCoeReal`. Lean proof by Matteo Cipollina, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Thermodynamics/Temperature/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Coercion to `ℝ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
/-- Coercion to `ℝ`. -/
noncomputable instance Temperature.instCoeReal : Coe Temperature ℝ := ⟨toReal⟩
