import AFTD.Prelude
import AFTD.Kb.Physics.EuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupInstGroup
import AFTD.Kb.Physics.EuclideanGroupOneTranslation

/-!
# EuclideanGroup.one_linear

Topic: classical_mechanics   Node: 3df39fb5b7aa

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.one_linear`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/Basic.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

EuclideanGroup.one_linear
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[simp] lemma EuclideanGroup.one_linear : (1 : EuclideanGroup n).linear = 1 := rfl
