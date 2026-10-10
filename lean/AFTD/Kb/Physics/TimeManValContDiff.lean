import AFTD.Prelude
import AFTD.Kb.Physics.TimeMan
import AFTD.Kb.Physics.TimeManInstTopologicalSpace
import AFTD.Kb.Physics.TimeManInstChartedSpaceReal
import AFTD.Kb.Physics.TimeManInstIsManifoldRealModelWithCornersSelfTopWithTopENat
import AFTD.Kb.Physics.TimeManValRange

/-!
# TimeMan.val_contDiff

Topic: classical_mechanics   Node: 0b3b616e71b9

Provenance: formalization of a published result. Source: Physlib, `TimeMan.val_contDiff`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Time/TimeMan.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TimeMan.val_contDiff
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold ContDiff in
lemma TimeMan.val_contDiff : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ω TimeMan.val := by
  refine contMDiffOn_univ.mp ?_
  exact contMDiffOn_chart (x := (⟨0⟩ : TimeMan))
