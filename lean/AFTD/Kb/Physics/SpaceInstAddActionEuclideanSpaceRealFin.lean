import AFTD.Prelude
import AFTD.Kb.Physics.Space
import AFTD.Kb.Physics.SpaceInstVAddEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceEqOfApply
import AFTD.Kb.Physics.SpaceVaddApply
import AFTD.Kb.Physics.SpaceValEqIff
import AFTD.Kb.Physics.SpaceVaddVal
import AFTD.Kb.Physics.SpaceInstCoeFunForallFinReal
import AFTD.Kb.Physics.SpaceInstNonempty
import AFTD.Kb.Physics.SpaceInstSubsingletonOfNatNat

/-!
# Space.instAddActionEuclideanSpaceRealFin

Topic: classical_mechanics   Node: cdf29c31f185

Provenance: formalization of a published result. Source: Physlib, `Space.instAddActionEuclideanSpaceRealFin`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Space.instAddActionEuclideanSpaceRealFin
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
noncomputable instance Space.instAddActionEuclideanSpaceRealFin : AddAction (EuclideanSpace ℝ (Fin d)) (Space d) where
  zero_vadd s := by
    ext i
    simp
  add_vadd v1 v2 s := by
    ext i
    simp only [vadd_apply, PiLp.add_apply]
    ring
