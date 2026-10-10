import AFTD.Prelude
import AFTD.Kb.Physics.EuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupInstGroup
import AFTD.Kb.Physics.EuclideanGroupTranslationVectorIncl
import AFTD.Kb.Physics.EuclideanGroupOneTranslation
import AFTD.Kb.Physics.EuclideanGroupOneLinear
import AFTD.Kb.Physics.EuclideanGroupMulTranslation
import AFTD.Kb.Physics.EuclideanGroupMulLinear

/-!
# EuclideanGroup.translation_zero

Topic: classical_mechanics   Node: 190ef009f0d7

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.translation_zero`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/Basic.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The translation by the zero vector is the identity of the Euclidean group.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The translation by the zero vector is the identity of the Euclidean group. -/
lemma EuclideanGroup.translation_zero : translationVector.incl n
    (Multiplicative.ofAdd (0 : EuclideanSpace ℝ (Fin n))) = 1 := by
  simp
