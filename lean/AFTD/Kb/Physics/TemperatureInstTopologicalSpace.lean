import AFTD.Prelude
import AFTD.Kb.Physics.Temperature
import AFTD.Kb.Physics.TemperatureInstCoeNNReal
import AFTD.Kb.Physics.TemperatureInstCoeReal

/-!
# Temperature.instTopologicalSpace

Topic: statistical_mechanics   Node: e8d85bca20f2

Provenance: formalization of a published result. Source: Physlib, `Temperature.instTopologicalSpace`. Lean proof by Matteo Cipollina, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Thermodynamics/Temperature/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Topology on `Temperature` induced from `ℝ≥0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
/-- Topology on `Temperature` induced from `ℝ≥0`. -/
instance Temperature.instTopologicalSpace : TopologicalSpace Temperature :=
  TopologicalSpace.induced (fun T : Temperature => (T.val : ℝ≥0)) inferInstance
