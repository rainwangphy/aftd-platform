import AFTD.Prelude
import AFTD.Kb.Physics.UnitaryOneParameterGroup
import AFTD.Kb.Physics.UnitaryOneParameterGroupInstCoeFunForallRealContinuousLinearMapComplexId
import AFTD.Kb.Physics.UnitaryOneParameterGroupGenerator
import AFTD.Kb.Physics.OneParameterSubgroupGeneratorUnique
import AFTD.Kb.Physics.UnitaryOneParameterGroupAdjointEq

/-!
# UnitaryOneParameterGroup.generator_unique

Topic: classical_mechanics   Node: 0c5e6f855443

Provenance: formalization of a published result. Source: Physlib, `UnitaryOneParameterGroup.generator_unique`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/OneParameterSubgroups/Unitary.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Any exponential generator of a unitary one-parameter group equals `U.generator`; the uniqueness of the derivative at zero (`OneParameterSubgroup.generator_unique`) is the underlying fact, restated here in terms of the physics convention.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open UnitaryOneParameterGroup in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- Any exponential generator of a unitary one-parameter group equals `U.generator`; the uniqueness of the derivative at zero (`OneParameterSubgroup.generator_unique`) is the underlying fact, restated here in terms of the physics convention. -/
lemma UnitaryOneParameterGroup.generator_unique (U : UnitaryOneParameterGroup H) (A : H →L[ℂ] H)
    (h : ∀ t : ℝ, U t = NormedSpace.exp ((-(t : ℂ) * Complex.I) • A)) :
    A = U.generator := by
  have hrep : ∀ t : ℝ, U t =
      NormedSpace.exp ((t : ℂ) • ((-Complex.I) • A)) := by
    intro t
    rw [h t]
    congr 1
    rw [smul_smul]
    congr 1
    ring
  have hderiv : (-Complex.I) • A = deriv U 0 :=
    OneParameterSubgroup.generator_unique U.toAddChar ((-Complex.I) • A)
      (fun t => by simpa only [Complex.coe_smul] using hrep t)
  calc
    A = Complex.I • ((-Complex.I) • A) := by rw [smul_smul]; simp
    _ = Complex.I • deriv U 0 := by rw [hderiv]
    _ = U.generator := rfl
