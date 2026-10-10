import AFTD.Prelude
import AFTD.Kb.Physics.EuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupInstGroup
import AFTD.Kb.Physics.EuclideanGroupOneTranslation
import AFTD.Kb.Physics.EuclideanGroupOneLinear

/-!
# EuclideanGroup.mul_translation

Topic: classical_mechanics   Node: e7a1558cd07f

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.mul_translation`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/Basic.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

EuclideanGroup.mul_translation
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[simp] lemma EuclideanGroup.mul_translation (A B : EuclideanGroup n) :
    (A * B).translation = A.translation + A.linear • B.translation := rfl
