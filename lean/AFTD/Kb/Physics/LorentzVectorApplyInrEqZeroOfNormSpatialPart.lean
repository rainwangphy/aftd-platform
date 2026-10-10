import AFTD.Prelude
import AFTD.Kb.Physics.LorentzVector
import AFTD.Kb.Physics.LorentzVectorSpatialPart
import AFTD.Kb.Physics.LorentzVectorSpatialPartApplyEqToCoord
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
import AFTD.Kb.Physics.LorentzVectorInstAddCommMonoid
import AFTD.Kb.Physics.LorentzVectorInstModuleReal
import AFTD.Kb.Physics.LorentzVectorInstAddCommGroup
import AFTD.Kb.Physics.LorentzVectorInstFiniteDimensionalReal
import AFTD.Kb.Physics.LorentzVectorInstNorm
import AFTD.Kb.Physics.LorentzVectorIsNormedAddCommGroup
import AFTD.Kb.Physics.LorentzVectorIsNormedSpace
import AFTD.Kb.Physics.LorentzVectorInstInnerReal
import AFTD.Kb.Physics.LorentzVectorInnerProductSpace
import AFTD.Kb.Physics.LorentzVectorInstChartedSpace
import AFTD.Kb.Physics.LorentzVectorInstCoeFunForallSumFinOfNatNatReal

/-!
# Lorentz.Vector.apply_inr_eq_zero_of_norm_spatialPart

Topic: special_relativity   Node: 3b73b526f1ba

Provenance: formalization of a published result. Source: Physlib, `Lorentz.Vector.apply_inr_eq_zero_of_norm_spatialPart`. Lean proof by Matteo Cipollina, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/Vector/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The spatial components of a vector whose spatial part has zero norm vanish.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
open Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
open InnerProductSpace in
open InnerProductSpace in
/-- The spatial components of a vector whose spatial part has zero norm vanish. -/
lemma Lorentz.Vector.apply_inr_eq_zero_of_norm_spatialPart {d : ℕ} {u : Vector d} (h : ‖u.spatialPart‖ = 0)
    (i : Fin d) : u (Sum.inr i) = 0 := by
  have := congrArg (fun x : EuclideanSpace ℝ (Fin d) => x i) (norm_eq_zero.mp h)
  simpa [spatialPart_apply_eq_toCoord] using this
