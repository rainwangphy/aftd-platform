import AFTD.Prelude
import AFTD.Kb.Physics.Time
import AFTD.Kb.Physics.TimeInstMetricSpace
import AFTD.Kb.Physics.TimeInstChartedSpaceReal
import AFTD.Kb.Physics.TimeInstAddTorsorReal
import AFTD.Kb.Physics.TimeVaddVal
import AFTD.Kb.Physics.TimeVsubEqVal
import AFTD.Kb.Physics.TimeInstNonempty
import AFTD.Kb.Physics.TimeInstVAddReal
import AFTD.Kb.Physics.TimeInstVSubReal
import AFTD.Kb.Physics.TimeInstNormedAddTorsorReal

/-!
# Time.instIsManifoldRealModelWithCornersSelfTopWithTopENat

Topic: classical_mechanics   Node: a330cbb0e1db

Provenance: formalization of a published result. Source: Physlib, `Time.instIsManifoldRealModelWithCornersSelfTopWithTopENat`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Time/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Time.instIsManifoldRealModelWithCornersSelfTopWithTopENat
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped Manifold ContDiff in
noncomputable instance Time.instIsManifoldRealModelWithCornersSelfTopWithTopENat : IsManifold 𝓘(ℝ, ℝ) ω Time := by
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨_, rfl⟩ ⟨_, rfl⟩
  exact contDiff_id.add contDiff_const |>.sub contDiff_const |>.contDiffOn
