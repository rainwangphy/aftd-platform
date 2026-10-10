import AFTD.Prelude
import AFTD.Kb.Physics.Space
import AFTD.Kb.Physics.SpaceInstPseudoMetricSpace
import AFTD.Kb.Physics.SpaceInstAddTorsorEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceValEqIff
import AFTD.Kb.Physics.SpaceVaddVal
import AFTD.Kb.Physics.SpaceVaddApply
import AFTD.Kb.Physics.SpaceVsubApply
import AFTD.Kb.Physics.SpaceInstCoeFunForallFinReal
import AFTD.Kb.Physics.SpaceInstNonempty
import AFTD.Kb.Physics.SpaceInstSubsingletonOfNatNat
import AFTD.Kb.Physics.SpaceInstVAddEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstAddActionEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstVSubEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstDist

/-!
# Space.instNormedAddTorsorEuclideanSpaceRealFin

Topic: classical_mechanics   Node: 91b1b639a169

Provenance: formalization of a published result. Source: Physlib, `Space.instNormedAddTorsorEuclideanSpaceRealFin`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Space.instNormedAddTorsorEuclideanSpaceRealFin
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
noncomputable instance Space.instNormedAddTorsorEuclideanSpaceRealFin {d} : NormedAddTorsor (EuclideanSpace ℝ (Fin d)) (Space d) where
  dist_eq_norm' p q := by simp [dist, EuclideanSpace.norm_eq]
