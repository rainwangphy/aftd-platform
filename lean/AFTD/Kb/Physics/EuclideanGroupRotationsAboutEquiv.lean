import AFTD.Prelude
import AFTD.Kb.Physics.EuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupInstGroup
import AFTD.Kb.Physics.EuclideanGroupRotationsAbout
import AFTD.Kb.Physics.EuclideanGroupRotationGroup
import AFTD.Kb.Physics.EuclideanGroupRotationsAboutToOrigin
import AFTD.Kb.Physics.EuclideanGroupRotationsAboutFromOrigin
import AFTD.Kb.Physics.EuclideanGroupRotationsAboutFromOriginCompToOrigin
import AFTD.Kb.Physics.EuclideanGroupRotationsAboutToOriginCompFromOrigin
import AFTD.Kb.Physics.EuclideanGroupOneTranslation
import AFTD.Kb.Physics.EuclideanGroupOneLinear
import AFTD.Kb.Physics.EuclideanGroupMulTranslation
import AFTD.Kb.Physics.EuclideanGroupMulLinear

/-!
# EuclideanGroup.RotationsAboutEquiv

Topic: classical_mechanics   Node: 757148c73939

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.RotationsAboutEquiv`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/Basic.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

API feature: conjugation by the translation `T(p)` exhibits the rotations about `p` as isomorphic to the rotations about the origin `RotationGroup n`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open EuclideanGroup in
variable {n} (p : EuclideanSpace ℝ (Fin n)) in
/-- API feature: conjugation by the translation `T(p)` exhibits the rotations about `p` as isomorphic to the rotations about the origin `RotationGroup n`. -/
noncomputable def EuclideanGroup.RotationsAboutEquiv : RotationsAbout p ≃* RotationGroup n :=
  MonoidHom.toMulEquiv (RotationsAbout.toOrigin p) (RotationsAbout.fromOrigin p)
    (RotationsAbout.fromOrigin_comp_toOrigin p) (RotationsAbout.toOrigin_comp_fromOrigin p)
