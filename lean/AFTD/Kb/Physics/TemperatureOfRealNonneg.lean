import AFTD.Prelude
import AFTD.Kb.Physics.Temperature
import AFTD.Kb.Physics.TemperatureOfNNReal
import AFTD.Kb.Physics.TemperatureBetaOfBeta
import AFTD.Kb.Physics.TemperatureOfBetaBeta
import AFTD.Kb.Physics.TemperatureOfNNRealVal
import AFTD.Kb.Physics.TemperatureCoeOfNNRealCoe
import AFTD.Kb.Physics.TemperatureCoeOfNNRealReal
import AFTD.Kb.Physics.TemperatureInstCoeNNReal
import AFTD.Kb.Physics.TemperatureInstCoeReal
import AFTD.Kb.Physics.TemperatureInstTopologicalSpace
import AFTD.Kb.Physics.TemperatureInstZero

/-!
# Temperature.ofRealNonneg

Topic: statistical_mechanics   Node: 7e919be0c2bc

Provenance: formalization of a published result. Source: Physlib, `Temperature.ofRealNonneg`. Lean proof by Matteo Cipollina, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Thermodynamics/Temperature/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Convenience: build a temperature from a real together with a proof of nonnegativity.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
open Filter Topology in
open Filter Topology in
/-- Convenience: build a temperature from a real together with a proof of nonnegativity. -/
@[simp]
noncomputable def Temperature.ofRealNonneg (t : ℝ) (ht : 0 ≤ t) : Temperature :=
  ofNNReal ⟨t, ht⟩
