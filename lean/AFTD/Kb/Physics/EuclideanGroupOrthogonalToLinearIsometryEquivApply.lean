import AFTD.Prelude
import AFTD.Kb.Physics.EuclideanGroupOrthogonalToLinearIsometryEquiv
import AFTD.Kb.Physics.EuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupOneTranslation
import AFTD.Kb.Physics.EuclideanGroupOneLinear
import AFTD.Kb.Physics.EuclideanGroupMulTranslation
import AFTD.Kb.Physics.EuclideanGroupMulLinear
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationTranslation
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationLinear
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationDecompose
import AFTD.Kb.Physics.EuclideanGroupInstGroup

/-!
# EuclideanGroup.orthogonalToLinearIsometryEquiv_apply

Topic: classical_mechanics   Node: 839823ed91db

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.orthogonalToLinearIsometryEquiv_apply`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/AffineGroup.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

EuclideanGroup.orthogonalToLinearIsometryEquiv_apply
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open EuclideanGroup in
variable {n : ℕ} in
@[simp] lemma EuclideanGroup.orthogonalToLinearIsometryEquiv_apply
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    orthogonalToLinearIsometryEquiv Q x = Q • x := rfl
