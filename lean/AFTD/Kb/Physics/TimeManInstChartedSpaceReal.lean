import AFTD.Prelude
import AFTD.Kb.Physics.TimeMan
import AFTD.Kb.Physics.TimeManInstTopologicalSpace
import AFTD.Kb.Physics.TimeManValHomeomorphism
import AFTD.Kb.Physics.TimeManValRange

/-!
# TimeMan.instChartedSpaceReal

Topic: classical_mechanics   Node: 54e1e925dc3c

Provenance: formalization of a published result. Source: Physlib, `TimeMan.instChartedSpaceReal`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Time/TimeMan.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The structure of a charted space on `TimeMan`
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The structure of a charted space on `TimeMan` -/
instance TimeMan.instChartedSpaceReal : ChartedSpace ℝ TimeMan where
  atlas := { valHomeomorphism.toOpenPartialHomeomorph }
  chartAt _ := valHomeomorphism.toOpenPartialHomeomorph
  mem_chart_source := by
    simp
  chart_mem_atlas := by
    intro x
    simp
