import AFTD.Prelude
import AFTD.Kb.Physics.EuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupSpecialOrthogonalIncl
import AFTD.Kb.Physics.EuclideanGroupOneTranslation
import AFTD.Kb.Physics.EuclideanGroupOneLinear
import AFTD.Kb.Physics.EuclideanGroupMulTranslation
import AFTD.Kb.Physics.EuclideanGroupMulLinear
import AFTD.Kb.Physics.EuclideanGroupInstGroup

/-!
# EuclideanGroup.ofRotationTranslation

Topic: classical_mechanics   Node: d516d080ebc6

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.ofRotationTranslation`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/Basic.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Specialization to a group element from a rotation and a translation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open EuclideanGroup in
variable {n} (p : EuclideanSpace ℝ (Fin n)) in
/-- Specialization to a group element from a rotation and a translation. -/
def EuclideanGroup.ofRotationTranslation (Q : Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (t : EuclideanSpace ℝ (Fin n)) : EuclideanGroup n :=
  ⟨t, specialOrthogonal.incl n Q⟩
