import AFTD.Prelude
import AFTD.Kb.Physics.TemperatureToReal
import AFTD.Kb.Physics.Temperature
import AFTD.Kb.Physics.TemperatureBetaOfBeta
import AFTD.Kb.Physics.TemperatureOfBetaBeta
import AFTD.Kb.Physics.TemperatureOfNNReal
import AFTD.Kb.Physics.TemperatureOfNNRealVal
import AFTD.Kb.Physics.TemperatureCoeOfNNRealCoe
import AFTD.Kb.Physics.TemperatureInstCoeNNReal
import AFTD.Kb.Physics.TemperatureInstCoeReal
import AFTD.Kb.Physics.TemperatureInstTopologicalSpace
import AFTD.Kb.Physics.TemperatureInstZero

/-!
# Temperature.coe_ofNNReal_real

Topic: statistical_mechanics   Node: 81a2aea747d9

Provenance: formalization of a published result. Source: Physlib, `Temperature.coe_ofNNReal_real`. Lean proof by Matteo Cipollina, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Thermodynamics/Temperature/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Temperature.coe_ofNNReal_real
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
open Filter Topology in
open Filter Topology in
@[simp]
lemma Temperature.coe_ofNNReal_real (t : ℝ≥0) : ((⟨t⟩ : Temperature) : ℝ) = t := rfl
