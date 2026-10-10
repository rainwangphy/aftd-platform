import AFTD.Prelude
import AFTD.Kb.Physics.EuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupInstGroup
import AFTD.Kb.Physics.EuclideanGroupRotationGroup
import AFTD.Kb.Physics.EuclideanGroupSpecialOrthogonalFromRotation
import AFTD.Kb.Physics.EuclideanGroupSpecialOrthogonalToRotation
import AFTD.Kb.Physics.EuclideanGroupOneTranslation
import AFTD.Kb.Physics.EuclideanGroupOneLinear
import AFTD.Kb.Physics.EuclideanGroupMulTranslation
import AFTD.Kb.Physics.EuclideanGroupMulLinear
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationTranslation
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationLinear
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationDecompose

/-!
# EuclideanGroup.specialOrthogonal.fromRotation_comp_toRotation

Topic: classical_mechanics   Node: c2b2c7d7472d

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.specialOrthogonal.fromRotation_comp_toRotation`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/Basic.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`specialOrthogonal.toRotation n` followed by `specialOrthogonal.fromRotation n` is the identity; the forward leg of the isomorphism `specialOrthogonalEquiv`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open EuclideanGroup in
variable {n} (p : EuclideanSpace ℝ (Fin n)) in
/-- `specialOrthogonal.toRotation n` followed by `specialOrthogonal.fromRotation n` is the identity; the forward leg of the isomorphism `specialOrthogonalEquiv`. -/
lemma EuclideanGroup.specialOrthogonal.fromRotation_comp_toRotation :
    (specialOrthogonal.fromRotation n).comp (specialOrthogonal.toRotation n) =
      MonoidHom.id (Matrix.specialOrthogonalGroup (Fin n) ℝ) := by
  apply MonoidHom.ext
  intro x
  rfl
