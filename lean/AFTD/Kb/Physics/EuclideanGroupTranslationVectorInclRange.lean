import AFTD.Prelude
import AFTD.Kb.Physics.EuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupInstGroup
import AFTD.Kb.Physics.EuclideanGroupTranslationVectorIncl
import AFTD.Kb.Physics.EuclideanGroupTranslationGroup
import AFTD.Kb.Physics.EuclideanGroupOneTranslation
import AFTD.Kb.Physics.EuclideanGroupOneLinear
import AFTD.Kb.Physics.EuclideanGroupMulTranslation
import AFTD.Kb.Physics.EuclideanGroupMulLinear

/-!
# EuclideanGroup.translationVector.incl_range

Topic: classical_mechanics   Node: 0fbdfedc8f05

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.translationVector.incl_range`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/Basic.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An API feature: the translation vector inclusion image is the `TranslationGroup` carrier.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- An API feature: the translation vector inclusion image is the `TranslationGroup` carrier. -/
lemma EuclideanGroup.translationVector.incl_range :
    Set.range (@translationVector.incl n) = (TranslationGroup n : Set (EuclideanGroup n)) := by
  ext g
  constructor
  · rintro ⟨v, hv⟩
    show g.linear.val = 1
    rw [← hv]
    rfl
  · intro h
    rw [Set.mem_range]
    refine ⟨g.translation, ?_⟩
    show (⟨g.translation, 1⟩ : EuclideanGroup n) = g
    refine EuclideanGroup.ext rfl ?_
    apply Subtype.ext
    simp [h.symm]
