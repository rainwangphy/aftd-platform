import AFTD.Prelude
import AFTD.Kb.Physics.LorentzVector
import AFTD.Kb.Physics.LorentzVectorInstAddCommGroup
import AFTD.Kb.Physics.LorentzVectorInstAddCommMonoid
import AFTD.Kb.Physics.LorentzVectorInstModuleReal
import AFTD.Kb.Physics.LorentzVectorBasis
import AFTD.Kb.Physics.LorentzVectorIsNormedAddCommGroup
import AFTD.Kb.Physics.LorentzVectorTimeComponent
import AFTD.Kb.Physics.LorentzVectorIsNormedSpace
import AFTD.Kb.Physics.LorentzVectorEquivEuclidApply
import AFTD.Kb.Physics.LorentzVectorAbsComponentLeNorm
import AFTD.Kb.Physics.LorentzVectorApplySmul
import AFTD.Kb.Physics.LorentzVectorApplyAdd
import AFTD.Kb.Physics.LorentzVectorApplySub
import AFTD.Kb.Physics.LorentzVectorNegApply
import AFTD.Kb.Physics.LorentzVectorZeroApply
import AFTD.Kb.Physics.LorentzVectorEquivPiApply
import AFTD.Kb.Physics.LorentzVectorFderivCoord
import AFTD.Kb.Physics.LorentzVectorBasisApply
import AFTD.Kb.Physics.LorentzVectorSpatialCLMBasisSumInl
import AFTD.Kb.Physics.LorentzVectorSpatialCLMBasisSumInr
import AFTD.Kb.Physics.LorentzVectorTemporalCLMBasisSumInr
import AFTD.Kb.Physics.LorentzVectorTemporalCLMBasisSumInl
import AFTD.Kb.Physics.LorentzVectorInstFiniteDimensionalReal
import AFTD.Kb.Physics.LorentzVectorInstNorm
import AFTD.Kb.Physics.LorentzVectorInstInnerReal
import AFTD.Kb.Physics.LorentzVectorInnerProductSpace
import AFTD.Kb.Physics.LorentzVectorInstChartedSpace
import AFTD.Kb.Physics.LorentzVectorInstCoeFunForallSumFinOfNatNatReal
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumPotentialEnergy

/-!
# Lorentz.Vector.ofTemporalComponent

Topic: special_relativity   Node: 25df74ff025e

Provenance: formalization of a published result. Source: Physlib, `Lorentz.Vector.ofTemporalComponent`. Lean proof by Matteo Cipollina, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/Vector/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The continuous linear map corresponding to the creation of a Lorentz Vector with only a non-zero temporal component.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
open Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
open InnerProductSpace in
/-- The continuous linear map corresponding to the creation of a Lorentz Vector with only a non-zero temporal component. -/
noncomputable def Lorentz.Vector.ofTemporalComponent {d : ℕ} : ℝ →L[ℝ] Vector d where
  toFun xt := xt • basis (Sum.inl 0)
  map_add' := by simp [add_smul]
  map_smul' := by simp [smul_smul]
