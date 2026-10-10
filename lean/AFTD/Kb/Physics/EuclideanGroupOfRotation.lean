import AFTD.Prelude
import AFTD.Kb.Physics.EuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupSpecialOrthogonalIncl
import AFTD.Kb.Physics.EuclideanGroupOneTranslation
import AFTD.Kb.Physics.EuclideanGroupOneLinear
import AFTD.Kb.Physics.EuclideanGroupMulTranslation
import AFTD.Kb.Physics.EuclideanGroupMulLinear
import AFTD.Kb.Physics.EuclideanGroupInstGroup

/-!
# EuclideanGroup.ofRotation

Topic: classical_mechanics   Node: 5f733f699f51

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.ofRotation`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/Basic.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Euclidean group element given by a rotation about the origin (zero translation).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open EuclideanGroup in
variable {n} (p : EuclideanSpace ℝ (Fin n)) in
/-- The Euclidean group element given by a rotation about the origin (zero translation). -/
def EuclideanGroup.ofRotation (Q : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    EuclideanGroup n := ⟨0, specialOrthogonal.incl n Q⟩
