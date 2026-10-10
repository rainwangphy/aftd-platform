import AFTD.Prelude
import AFTD.Kb.Physics.Time
import AFTD.Kb.Physics.TimeInstMetricSpace
import AFTD.Kb.Physics.TimeInstNormedAddTorsorReal
import AFTD.Kb.Physics.TimeInstAddTorsorReal
import AFTD.Kb.Physics.TimeVaddVal
import AFTD.Kb.Physics.TimeVsubEqVal
import AFTD.Kb.Physics.TimeInstNonempty
import AFTD.Kb.Physics.TimeInstVAddReal
import AFTD.Kb.Physics.TimeInstVSubReal

/-!
# Time.instChartedSpaceReal

Topic: classical_mechanics   Node: 0d5d48e67c76

Provenance: formalization of a published result. Source: Physlib, `Time.instChartedSpaceReal`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Time/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Time.instChartedSpaceReal
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped Manifold ContDiff in
noncomputable instance Time.instChartedSpaceReal : ChartedSpace ℝ Time :=
  let chartAt t := (Homeomorph.vaddConst t).symm.toOpenPartialHomeomorph
  { chartAt,
    atlas := Set.range chartAt,
    mem_chart_source := Set.mem_univ,
    chart_mem_atlas := by simp }
