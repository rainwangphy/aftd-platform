import AFTD.Prelude
import AFTD.Kb.Physics.EuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupInstGroup
import AFTD.Kb.Physics.EuclideanGroupRotationsAbout
import AFTD.Kb.Physics.EuclideanGroupRotationGroup
import AFTD.Kb.Physics.EuclideanGroupRotationsAboutFromOrigin
import AFTD.Kb.Physics.EuclideanGroupRotationsAboutToOrigin
import AFTD.Kb.Physics.EuclideanGroupTranslationVectorIncl
import AFTD.Kb.Physics.EuclideanGroupOneTranslation
import AFTD.Kb.Physics.EuclideanGroupOneLinear
import AFTD.Kb.Physics.EuclideanGroupMulTranslation
import AFTD.Kb.Physics.EuclideanGroupMulLinear

/-!
# EuclideanGroup.RotationsAbout.fromOrigin_comp_toOrigin

Topic: classical_mechanics   Node: 7d37aec944b6

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.RotationsAbout.fromOrigin_comp_toOrigin`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/Basic.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`RotationsAbout.toOrigin p` followed by `RotationsAbout.fromOrigin p` is the identity; the forward leg of the isomorphism `RotationsAboutEquiv`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open EuclideanGroup in
variable {n} (p : EuclideanSpace ℝ (Fin n)) in
/-- `RotationsAbout.toOrigin p` followed by `RotationsAbout.fromOrigin p` is the identity; the forward leg of the isomorphism `RotationsAboutEquiv`. -/
lemma EuclideanGroup.RotationsAbout.fromOrigin_comp_toOrigin :
    (RotationsAbout.fromOrigin p).comp (RotationsAbout.toOrigin p) =
      MonoidHom.id (RotationsAbout p) := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.id_apply, SetLike.coe_eq_coe]
  unfold RotationsAbout.toOrigin
  unfold RotationsAbout.fromOrigin
  simp [mul_assoc]
