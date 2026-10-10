import AFTD.Prelude
import AFTD.Kb.Physics.EuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupInstGroup
import AFTD.Kb.Physics.EuclideanGroupToAffineIsometryMulEquiv
import AFTD.Kb.Physics.EuclideanGroupToAffineIsometryHom
import AFTD.Kb.Physics.EuclideanGroupOneTranslation
import AFTD.Kb.Physics.EuclideanGroupOneLinear
import AFTD.Kb.Physics.EuclideanGroupMulTranslation
import AFTD.Kb.Physics.EuclideanGroupMulLinear
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationTranslation
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationLinear
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationDecompose
import AFTD.Kb.Physics.EuclideanGroupOrthogonalToLinearIsometryEquivApply
import AFTD.Kb.Physics.EuclideanGroupToAffineIsometryHomApply
import AFTD.Kb.Physics.EuclideanGroupOrthogonalToLinearIsometryEquivLeftInv
import AFTD.Kb.Physics.EuclideanGroupLinearIsometryEquivConstVAddMul
import AFTD.Kb.Physics.EuclideanGroupOrthogonalToLinearIsometryEquivRightInv

/-!
# EuclideanGroup.toAffineIsometryMulEquiv_apply

Topic: classical_mechanics   Node: 709b45288fe4

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.toAffineIsometryMulEquiv_apply`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/AffineGroup.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`toAffineIsometryMulEquiv` agrees with `toAffineIsometryHom`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open EuclideanGroup in
variable {n : ℕ} in
/-- `toAffineIsometryMulEquiv` agrees with `toAffineIsometryHom`. -/
@[simp] lemma EuclideanGroup.toAffineIsometryMulEquiv_apply (A : EuclideanGroup n) :
    toAffineIsometryMulEquiv A = toAffineIsometryHom A := rfl
