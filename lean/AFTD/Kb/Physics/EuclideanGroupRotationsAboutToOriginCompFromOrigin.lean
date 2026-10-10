import AFTD.Prelude
import AFTD.Kb.Physics.EuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupInstGroup
import AFTD.Kb.Physics.EuclideanGroupRotationGroup
import AFTD.Kb.Physics.EuclideanGroupRotationsAbout
import AFTD.Kb.Physics.EuclideanGroupRotationsAboutToOrigin
import AFTD.Kb.Physics.EuclideanGroupRotationsAboutFromOrigin
import AFTD.Kb.Physics.EuclideanGroupTranslationVectorIncl
import AFTD.Kb.Physics.EuclideanGroupOneTranslation
import AFTD.Kb.Physics.EuclideanGroupOneLinear
import AFTD.Kb.Physics.EuclideanGroupMulTranslation
import AFTD.Kb.Physics.EuclideanGroupMulLinear

/-!
# EuclideanGroup.RotationsAbout.toOrigin_comp_fromOrigin

Topic: classical_mechanics   Node: 3fd709c49af8

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.RotationsAbout.toOrigin_comp_fromOrigin`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/Basic.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`RotationsAbout.fromOrigin p` followed by `RotationsAbout.toOrigin p` is the identity; the backward leg of the isomorphism `RotationsAboutEquiv`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open EuclideanGroup in
variable {n} (p : EuclideanSpace ℝ (Fin n)) in
/-- `RotationsAbout.fromOrigin p` followed by `RotationsAbout.toOrigin p` is the identity; the backward leg of the isomorphism `RotationsAboutEquiv`. -/
lemma EuclideanGroup.RotationsAbout.toOrigin_comp_fromOrigin :
    (RotationsAbout.toOrigin p).comp (RotationsAbout.fromOrigin p) =
      MonoidHom.id (RotationGroup n) := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.id_apply, SetLike.coe_eq_coe]
  unfold RotationsAbout.toOrigin
  unfold RotationsAbout.fromOrigin
  simp [mul_assoc]
