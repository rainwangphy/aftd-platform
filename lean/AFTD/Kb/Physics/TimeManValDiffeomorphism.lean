import AFTD.Prelude
import AFTD.Kb.Physics.TimeMan
import AFTD.Kb.Physics.TimeManInstTopologicalSpace
import AFTD.Kb.Physics.TimeManInstChartedSpaceReal
import AFTD.Kb.Physics.TimeManValHomeomorphism
import AFTD.Kb.Physics.TimeManInstIsManifoldRealModelWithCornersSelfTopWithTopENat
import AFTD.Kb.Physics.TimeManValContDiff
import AFTD.Kb.Physics.TimeManValRange
import AFTD.Kb.Physics.Time

/-!
# TimeMan.valDiffeomorphism

Topic: classical_mechanics   Node: 35bdebecc593

Provenance: formalization of a published result. Source: Physlib, `TimeMan.valDiffeomorphism`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Time/TimeMan.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The choice of map `Time.val` from `TimeMan` to `ℝ` as a diffeomorphism.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold ContDiff in
/-- The choice of map `Time.val` from `TimeMan` to `ℝ` as a diffeomorphism. -/
noncomputable def TimeMan.valDiffeomorphism : TimeMan ≃ₘ^ω⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ ℝ where
  toEquiv := valHomeomorphism.toEquiv
  contMDiff_toFun := val_contDiff
  contMDiff_invFun := by
    refine contMDiffOn_univ.mp ?_
    exact contMDiffOn_chart_symm (x := (⟨0⟩ : TimeMan))
