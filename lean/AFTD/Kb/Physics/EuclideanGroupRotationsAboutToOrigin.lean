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
# EuclideanGroup.RotationsAbout.toOrigin

Topic: classical_mechanics   Node: 48d04d3c2d22

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.RotationsAbout.toOrigin`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/Basic.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Conjugate a rotation about `p` back to a rotation about the origin.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open EuclideanGroup in
variable {n} (p : EuclideanSpace ℝ (Fin n)) in
/-- Conjugate a rotation about `p` back to a rotation about the origin. -/
noncomputable def EuclideanGroup.RotationsAbout.toOrigin :
    RotationsAbout p →* RotationGroup n where
  toFun g := ⟨translationVector.incl n (Multiplicative.ofAdd (-p))
    * (g : EuclideanGroup n) * translationVector.incl n (Multiplicative.ofAdd p), by
      obtain ⟨g, hg⟩ := g
      obtain ⟨r, hr⟩ := hg
      simp; rw [hr]; simp [mul_assoc]⟩
  map_one' := by simp
  map_mul' := by
    intro x y
    obtain ⟨a, ha⟩ := x
    obtain ⟨b, hb⟩ := y
    obtain ⟨r1, hr1⟩ := ha
    obtain ⟨r2, hr2⟩ := hb
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [hr1, hr2]
    simp [mul_assoc]
