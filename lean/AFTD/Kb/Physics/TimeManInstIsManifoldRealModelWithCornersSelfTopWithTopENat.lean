import AFTD.Prelude
import AFTD.Kb.Physics.TimeMan
import AFTD.Kb.Physics.TimeManInstTopologicalSpace
import AFTD.Kb.Physics.TimeManInstChartedSpaceReal
import AFTD.Kb.Physics.TimeManValHomeomorphism
import AFTD.Kb.Physics.TimeManValRange
import AFTD.Kb.Physics.TimeInstIsManifoldRealModelWithCornersSelfTopWithTopENat
import AFTD.Kb.Physics.Time

/-!
# TimeMan.instIsManifoldRealModelWithCornersSelfTopWithTopENat

Topic: classical_mechanics   Node: 93e448b99cd9

Provenance: formalization of a published result. Source: Physlib, `TimeMan.instIsManifoldRealModelWithCornersSelfTopWithTopENat`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Time/TimeMan.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The structure of a manifold on `TimeMan` induced by the choice of map `Time.val`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold ContDiff in
/-- The structure of a manifold on `TimeMan` induced by the choice of map `Time.val`. -/
instance TimeMan.instIsManifoldRealModelWithCornersSelfTopWithTopENat : IsManifold 𝓘(ℝ, ℝ) ω TimeMan where
  compatible := by
    intro e1 e2 h1 h2
    simp [atlas, ChartedSpace.atlas] at h1 h2
    subst h1 h2
    exact symm_trans_mem_contDiffGroupoid valHomeomorphism.toOpenPartialHomeomorph
