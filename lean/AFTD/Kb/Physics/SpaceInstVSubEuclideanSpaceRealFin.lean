import AFTD.Prelude
import AFTD.Kb.Physics.Space
import AFTD.Kb.Physics.SpaceValEqIff
import AFTD.Kb.Physics.SpaceVaddVal
import AFTD.Kb.Physics.SpaceVaddApply
import AFTD.Kb.Physics.SpaceInstCoeFunForallFinReal
import AFTD.Kb.Physics.SpaceInstNonempty
import AFTD.Kb.Physics.SpaceInstSubsingletonOfNatNat
import AFTD.Kb.Physics.SpaceInstVAddEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstAddActionEuclideanSpaceRealFin

/-!
# Space.instVSubEuclideanSpaceRealFin

Topic: classical_mechanics   Node: 73118565d716

Provenance: formalization of a published result. Source: Physlib, `Space.instVSubEuclideanSpaceRealFin`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Space.instVSubEuclideanSpaceRealFin
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
noncomputable instance Space.instVSubEuclideanSpaceRealFin {d} : VSub (EuclideanSpace ℝ (Fin d)) (Space d) where
  vsub s1 s2 := WithLp.toLp 2 <| fun i => s1 i - s2 i
