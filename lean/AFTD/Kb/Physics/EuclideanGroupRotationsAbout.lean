import AFTD.Prelude
import AFTD.Kb.Physics.EuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupInstGroup
import AFTD.Kb.Physics.EuclideanGroupRotationGroup
import AFTD.Kb.Physics.EuclideanGroupTranslationVectorIncl
import AFTD.Kb.Physics.EuclideanGroupOneTranslation
import AFTD.Kb.Physics.EuclideanGroupOneLinear
import AFTD.Kb.Physics.EuclideanGroupMulTranslation
import AFTD.Kb.Physics.EuclideanGroupMulLinear

/-!
# EuclideanGroup.RotationsAbout

Topic: classical_mechanics   Node: 37de07a045bd

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.RotationsAbout`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/Basic.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The subgroup of rotation about a spatial point `p : EuclideanSpace ℝ (Fin n)` consists of elements of the form T(p) * r * T(-p) with T(·) : translationVector.incl n (Multiplicative.ofAdd ·) and r : RotationGroup where r is viewed as a rotation about the origin. Note T(-p) = T(p)⁻¹.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open EuclideanGroup in
variable {n} (p : EuclideanSpace ℝ (Fin n)) in
/-- The subgroup of rotation about a spatial point `p : EuclideanSpace ℝ (Fin n)` consists of elements of the form T(p) * r * T(-p) with T(·) : translationVector.incl n (Multiplicative.ofAdd ·) and r : RotationGroup where r is viewed as a rotation about the origin. Note T(-p) = T(p)⁻¹. -/
noncomputable def EuclideanGroup.RotationsAbout : Subgroup (EuclideanGroup n) where
  carrier := {g | ∃ r : RotationGroup n, g = translationVector.incl n (Multiplicative.ofAdd p)
    * (r : EuclideanGroup n) * translationVector.incl n (Multiplicative.ofAdd (-p))}
  mul_mem' {a b} ha hb := by
    obtain ⟨r1, hr1⟩ := ha
    obtain ⟨r2, hr2⟩ := hb
    use r1 * r2
    rw [hr1, hr2]
    simp only [ofAdd_neg, map_inv, conj_mul, Subgroup.coe_mul]
  one_mem' := by
    simp; use 1
    constructor <;> simp
  inv_mem' {a} ha := by
    obtain ⟨ra, hra⟩ := ha
    use ra⁻¹
    rw [hra]
    simp [mul_inv_rev, mul_assoc]
