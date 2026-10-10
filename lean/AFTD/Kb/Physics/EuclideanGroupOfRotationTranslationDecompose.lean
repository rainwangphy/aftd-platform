import AFTD.Prelude
import AFTD.Kb.Physics.EuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslation
import AFTD.Kb.Physics.EuclideanGroupInstGroup
import AFTD.Kb.Physics.EuclideanGroupTranslationVectorIncl
import AFTD.Kb.Physics.EuclideanGroupOfRotation
import AFTD.Kb.Physics.EuclideanGroupSpecialOrthogonalIncl
import AFTD.Kb.Physics.EuclideanGroupOneTranslation
import AFTD.Kb.Physics.EuclideanGroupOneLinear
import AFTD.Kb.Physics.EuclideanGroupMulTranslation
import AFTD.Kb.Physics.EuclideanGroupMulLinear
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationTranslation
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationLinear

/-!
# EuclideanGroup.ofRotationTranslation_decompose

Topic: classical_mechanics   Node: 60e9df08f147

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.ofRotationTranslation_decompose`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/Basic.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

API feature: the inclusion image decomposes as group product.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open EuclideanGroup in
variable {n} (p : EuclideanSpace ℝ (Fin n)) in
/-- API feature: the inclusion image decomposes as group product. -/
@[simp]
lemma EuclideanGroup.ofRotationTranslation_decompose (Q : Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (t : EuclideanSpace ℝ (Fin n)) :
    (ofRotationTranslation Q t) =
    (translationVector.incl n (Multiplicative.ofAdd t)) * (ofRotation (Q)) := by
  refine EuclideanGroup.ext ?_ ?_
  · show t = t + (1 : Matrix.orthogonalGroup (Fin n) ℝ) • 0
    rw [smul_zero, add_zero]
  · show specialOrthogonal.incl n Q = 1 * specialOrthogonal.incl n Q
    rw [one_mul]
