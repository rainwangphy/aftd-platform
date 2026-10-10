import AFTD.Prelude
import AFTD.Kb.Physics.TimeMan
import AFTD.Kb.Physics.TimeManValRange
import AFTD.Kb.Physics.TimeManInstTopologicalSpace
import AFTD.Kb.Physics.TimeManInstChartedSpaceReal
import AFTD.Kb.Physics.TimeManInstIsManifoldRealModelWithCornersSelfTopWithTopENat

/-!
# TimeMan.instLE

Topic: classical_mechanics   Node: f95ab5eb6900

Provenance: formalization of a published result. Source: Physlib, `TimeMan.instLE`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Time/TimeMan.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The instance of an orientation on TimeMan.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold ContDiff in
/-- The instance of an orientation on TimeMan. -/
instance TimeMan.instLE : LE TimeMan where
  le x y := x.val ≤ y.val
