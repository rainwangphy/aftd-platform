import AFTD.Prelude
import AFTD.Kb.Physics.Space
import AFTD.Kb.Physics.SpaceInstSeminormedAddCommGroup
import AFTD.Kb.Physics.SpaceInstInnerReal
import AFTD.Kb.Physics.SpaceInstVAddEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstZero
import AFTD.Kb.Physics.SpaceEqVaddZero
import AFTD.Kb.Physics.SpaceNormVaddZero
import AFTD.Kb.Physics.SpaceInnerVaddZero
import AFTD.Kb.Physics.SpaceInstAddCommMonoid
import AFTD.Kb.Physics.SpaceInstModuleReal
import AFTD.Kb.Physics.SpaceSmulVaddZero
import AFTD.Kb.Physics.SpaceInnerApply
import AFTD.Kb.Physics.SpaceAddVaddZero
import AFTD.Kb.Physics.SpaceValEqIff
import AFTD.Kb.Physics.SpaceVaddVal
import AFTD.Kb.Physics.SpaceVaddApply
import AFTD.Kb.Physics.SpaceVsubApply
import AFTD.Kb.Physics.SpaceZeroVal
import AFTD.Kb.Physics.SpaceZeroApply
import AFTD.Kb.Physics.SpaceVectorToSpaceApply
import AFTD.Kb.Physics.SpaceVectorToSpaceVsubZero
import AFTD.Kb.Physics.SpaceChartEuclideanApply
import AFTD.Kb.Physics.SpaceAddVal
import AFTD.Kb.Physics.SpaceAddApply
import AFTD.Kb.Physics.SpaceNsmulVal
import AFTD.Kb.Physics.SpaceNsmulApply
import AFTD.Kb.Physics.SpaceSmulVal
import AFTD.Kb.Physics.SpaceSmulApply
import AFTD.Kb.Physics.SpaceAbsEvalLeNorm
import AFTD.Kb.Physics.SpaceNegVal
import AFTD.Kb.Physics.SpaceNegApply
import AFTD.Kb.Physics.SpaceSubApply
import AFTD.Kb.Physics.SpaceSubVal
import AFTD.Kb.Physics.SpaceVaddZeroSubVaddZero
import AFTD.Kb.Physics.SpaceDistEqNorm
import AFTD.Kb.Physics.SpaceInstCoeFunForallFinReal
import AFTD.Kb.Physics.SpaceInstNonempty
import AFTD.Kb.Physics.SpaceInstSubsingletonOfNatNat
import AFTD.Kb.Physics.SpaceInstAddActionEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstVSubEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstAddTorsorEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstDist
import AFTD.Kb.Physics.SpaceInstPseudoMetricSpace
import AFTD.Kb.Physics.SpaceInstNormedAddTorsorEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstMetricSpace
import AFTD.Kb.Physics.SpaceInstNontrivial
import AFTD.Kb.Physics.SpaceInstChartedSpaceEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstIsManifoldRealEuclideanSpaceFinModelWithCornersSelfTopWithTopENat
import AFTD.Kb.Physics.SpaceInstAdd
import AFTD.Kb.Physics.SpaceInstSMulReal
import AFTD.Kb.Physics.SpaceInstNorm
import AFTD.Kb.Physics.SpaceInstNeg
import AFTD.Kb.Physics.SpaceInstAddCommGroup
import AFTD.Kb.Physics.SpaceInstNormedAddCommGroup

/-!
# Space.instInnerProductSpaceReal

Topic: classical_mechanics   Node: bdf980e1ab2e

Provenance: formalization of a published result. Source: Physlib, `Space.instInnerProductSpaceReal`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Module.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Space.instInnerProductSpaceReal
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance Space.instInnerProductSpaceReal {d} : InnerProductSpace ℝ (Space d) where
  norm_smul_le a x := by
    obtain ⟨v, rfl⟩ := eq_vadd_zero x
    simpa only [smul_vadd_zero, norm_vadd_zero, Real.norm_eq_abs] using norm_smul_le a v
  norm_sq_eq_re_inner x := by
    obtain ⟨v, rfl⟩ := eq_vadd_zero x
    simp
  conj_inner_symm x y := by
    simp [inner_apply, mul_comm]
  add_left x y z := by
    obtain ⟨v1, rfl⟩ := eq_vadd_zero x
    obtain ⟨v2, rfl⟩ := eq_vadd_zero y
    obtain ⟨v3, rfl⟩ := eq_vadd_zero z
    simpa only [add_vadd_zero, inner_vadd_zero] using InnerProductSpace.add_left v1 v2 v3
  smul_left x y a := by
    obtain ⟨v1, rfl⟩ := eq_vadd_zero x
    obtain ⟨v2, rfl⟩ := eq_vadd_zero y
    simpa only [smul_vadd_zero, inner_vadd_zero, conj_trivial]
      using InnerProductSpace.smul_left v1 v2 a
