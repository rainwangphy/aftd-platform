import AFTD.Prelude
import AFTD.Kb.Physics.EuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupInstGroup
import AFTD.Kb.Physics.EuclideanGroupTranslationGroup
import AFTD.Kb.Physics.EuclideanGroupOneTranslation
import AFTD.Kb.Physics.EuclideanGroupOneLinear
import AFTD.Kb.Physics.EuclideanGroupMulTranslation
import AFTD.Kb.Physics.EuclideanGroupMulLinear

/-!
# EuclideanGroup.TranslationGroup.incl

Topic: classical_mechanics   Node: b72ee21e94ca

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.TranslationGroup.incl`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/Basic.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The inclusion of the translation subgroup into the Euclidean group.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The inclusion of the translation subgroup into the Euclidean group. -/
noncomputable def EuclideanGroup.TranslationGroup.incl (n : ℕ) :
    TranslationGroup n →* EuclideanGroup n := (TranslationGroup n).subtype
