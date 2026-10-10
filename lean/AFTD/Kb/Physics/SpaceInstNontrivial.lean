import AFTD.Prelude
import AFTD.Kb.Physics.Space
import AFTD.Kb.Physics.SpaceInstNonempty
import AFTD.Kb.Physics.SpaceInstVAddEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstAddTorsorEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceValEqIff
import AFTD.Kb.Physics.SpaceVaddVal
import AFTD.Kb.Physics.SpaceVaddApply
import AFTD.Kb.Physics.SpaceVsubApply
import AFTD.Kb.Physics.SpaceInstCoeFunForallFinReal
import AFTD.Kb.Physics.SpaceInstSubsingletonOfNatNat
import AFTD.Kb.Physics.SpaceInstAddActionEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstVSubEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstDist
import AFTD.Kb.Physics.SpaceInstPseudoMetricSpace
import AFTD.Kb.Physics.SpaceInstNormedAddTorsorEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstMetricSpace

/-!
# Space.instNontrivial

Topic: classical_mechanics   Node: 7e3ae340f58e

Provenance: formalization of a published result. Source: Physlib, `Space.instNontrivial`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Space.instNontrivial
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance Space.instNontrivial {d : ℕ} [NeZero d] : Nontrivial (Space d) where
  exists_pair_ne := by
    obtain k := Classical.choice Space.instNonempty
    obtain ⟨v1, hv⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin d))
    use k, v1 +ᵥ k
    simpa [ne_eq, eq_vadd_iff_vsub_eq, vsub_self] using hv.symm
