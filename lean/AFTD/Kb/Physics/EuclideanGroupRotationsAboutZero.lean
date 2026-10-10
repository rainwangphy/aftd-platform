import AFTD.Prelude
import AFTD.Kb.Physics.EuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupInstGroup
import AFTD.Kb.Physics.EuclideanGroupRotationsAbout
import AFTD.Kb.Physics.EuclideanGroupRotationGroup
import AFTD.Kb.Physics.EuclideanGroupTranslationVectorIncl
import AFTD.Kb.Physics.EuclideanGroupOneTranslation
import AFTD.Kb.Physics.EuclideanGroupOneLinear
import AFTD.Kb.Physics.EuclideanGroupMulTranslation
import AFTD.Kb.Physics.EuclideanGroupMulLinear

/-!
# EuclideanGroup.RotationsAbout_zero

Topic: classical_mechanics   Node: f6ae07b201bc

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.RotationsAbout_zero`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/Basic.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

API feature: the degenerate identity that `RotationsAbout 0 = RotationGroup n`
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open EuclideanGroup in
variable {n} (p : EuclideanSpace ℝ (Fin n)) in
/-- API feature: the degenerate identity that `RotationsAbout 0 = RotationGroup n` -/
lemma EuclideanGroup.RotationsAbout_zero : RotationsAbout (0 : EuclideanSpace ℝ (Fin n)) = RotationGroup n := by
  apply Subgroup.ext
  intro g
  constructor
  · intro hg
    obtain ⟨g1, hg1⟩ := hg
    simp at hg1
    rw [hg1]
    simp
  · intro hg
    use ⟨g, hg⟩
    simp
