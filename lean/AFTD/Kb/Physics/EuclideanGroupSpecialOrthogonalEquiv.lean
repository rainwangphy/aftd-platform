import AFTD.Prelude
import AFTD.Kb.Physics.EuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupInstGroup
import AFTD.Kb.Physics.EuclideanGroupRotationGroup
import AFTD.Kb.Physics.EuclideanGroupRotationsAboutToOrigin
import AFTD.Kb.Physics.EuclideanGroupSpecialOrthogonalToRotation
import AFTD.Kb.Physics.EuclideanGroupSpecialOrthogonalFromRotation
import AFTD.Kb.Physics.EuclideanGroupSpecialOrthogonalFromRotationCompToRotation
import AFTD.Kb.Physics.EuclideanGroupSpecialOrthogonalToRotationCompFromRotation
import AFTD.Kb.Physics.EuclideanGroupOneTranslation
import AFTD.Kb.Physics.EuclideanGroupOneLinear
import AFTD.Kb.Physics.EuclideanGroupMulTranslation
import AFTD.Kb.Physics.EuclideanGroupMulLinear
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationTranslation
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationLinear
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationDecompose

/-!
# EuclideanGroup.specialOrthogonalEquiv

Topic: classical_mechanics   Node: 6c9770cd2feb

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.specialOrthogonalEquiv`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/Basic.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

API feature: SO(n) ≃* RotationGroup n
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open EuclideanGroup in
variable {n} (p : EuclideanSpace ℝ (Fin n)) in
/-- API feature: SO(n) ≃* RotationGroup n -/
noncomputable def EuclideanGroup.specialOrthogonalEquiv :
    Matrix.specialOrthogonalGroup (Fin n) ℝ ≃* RotationGroup n :=
    MonoidHom.toMulEquiv (specialOrthogonal.toRotation n) (specialOrthogonal.fromRotation n)
    specialOrthogonal.fromRotation_comp_toRotation specialOrthogonal.toRotation_comp_fromRotation
