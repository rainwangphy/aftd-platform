import AFTD.Prelude
import AFTD.Kb.Physics.EuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupInstGroup
import AFTD.Kb.Physics.EuclideanGroupSpecialEuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupOneTranslation
import AFTD.Kb.Physics.EuclideanGroupOneLinear
import AFTD.Kb.Physics.EuclideanGroupMulTranslation
import AFTD.Kb.Physics.EuclideanGroupMulLinear

/-!
# EuclideanGroup.SpecialEuclideanGroup.incl

Topic: classical_mechanics   Node: 89c48777c74b

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.SpecialEuclideanGroup.incl`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/Basic.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The inclusion of the special Euclidean group into the Euclidean group.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The inclusion of the special Euclidean group into the Euclidean group. -/
noncomputable def EuclideanGroup.SpecialEuclideanGroup.incl (n : ℕ) :
    SpecialEuclideanGroup n →* EuclideanGroup n := (SpecialEuclideanGroup n).subtype
