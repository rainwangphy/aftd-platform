import AFTD.Prelude
import AFTD.Kb.Physics.EuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslation
import AFTD.Kb.Physics.EuclideanGroupSpecialOrthogonalIncl
import AFTD.Kb.Physics.EuclideanGroupOneTranslation
import AFTD.Kb.Physics.EuclideanGroupOneLinear
import AFTD.Kb.Physics.EuclideanGroupMulTranslation
import AFTD.Kb.Physics.EuclideanGroupMulLinear
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationTranslation
import AFTD.Kb.Physics.EuclideanGroupInstGroup

/-!
# EuclideanGroup.ofRotationTranslation_linear

Topic: classical_mechanics   Node: 243cd4bbeb48

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.ofRotationTranslation_linear`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/Basic.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The specialization projects back to the linear (rotation) component.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open EuclideanGroup in
variable {n} (p : EuclideanSpace ℝ (Fin n)) in
/-- The specialization projects back to the linear (rotation) component. -/
@[simp]
lemma EuclideanGroup.ofRotationTranslation_linear (Q : Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (t : EuclideanSpace ℝ (Fin n)) :
    (ofRotationTranslation Q t).linear = specialOrthogonal.incl n Q := rfl
