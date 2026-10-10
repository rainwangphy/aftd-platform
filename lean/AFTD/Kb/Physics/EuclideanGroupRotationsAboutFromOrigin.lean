import AFTD.Prelude
import AFTD.Kb.Physics.EuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupInstGroup
import AFTD.Kb.Physics.EuclideanGroupRotationGroup
import AFTD.Kb.Physics.EuclideanGroupRotationsAbout
import AFTD.Kb.Physics.EuclideanGroupTranslationVectorIncl
import AFTD.Kb.Physics.EuclideanGroupSpecialEuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupOriginStabilizer
import AFTD.Kb.Physics.EuclideanGroupRotationsAboutToOrigin
import AFTD.Kb.Physics.EuclideanGroupOneTranslation
import AFTD.Kb.Physics.EuclideanGroupOneLinear
import AFTD.Kb.Physics.EuclideanGroupMulTranslation
import AFTD.Kb.Physics.EuclideanGroupMulLinear

/-!
# EuclideanGroup.RotationsAbout.fromOrigin

Topic: classical_mechanics   Node: dfda0f3fdaa9

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.RotationsAbout.fromOrigin`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/Basic.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Conjugate a rotation about the origin to a rotation about `p`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open EuclideanGroup in
variable {n} (p : EuclideanSpace ℝ (Fin n)) in
/-- Conjugate a rotation about the origin to a rotation about `p`. -/
noncomputable def EuclideanGroup.RotationsAbout.fromOrigin :
    RotationGroup n →* RotationsAbout p where
  toFun g := ⟨translationVector.incl n (Multiplicative.ofAdd p)
    * (g : EuclideanGroup n) * translationVector.incl n (Multiplicative.ofAdd (-p)), by use g⟩
  map_one' := by simp
  map_mul' := by
    intro x y
    obtain ⟨a, ha⟩ := x
    obtain ⟨b, hb⟩ := y
    obtain ⟨r1, hr1⟩ := ha
    obtain ⟨r2, hr2⟩ := hb
    simp
