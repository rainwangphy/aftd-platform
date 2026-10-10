import AFTD.Prelude
import AFTD.Kb.Physics.LorentzCoVector
import AFTD.Kb.Physics.LorentzCoVectorInstAddCommMonoid
import AFTD.Kb.Physics.LorentzCoVectorInstModuleReal
import AFTD.Kb.Physics.LorentzCoVectorBasis
import AFTD.Kb.Physics.LorentzCoVectorApplySmul
import AFTD.Kb.Physics.LorentzCoVectorApplyAdd
import AFTD.Kb.Physics.LorentzCoVectorApplySub
import AFTD.Kb.Physics.LorentzCoVectorApplySum
import AFTD.Kb.Physics.LorentzCoVectorNegApply
import AFTD.Kb.Physics.LorentzCoVectorZeroApply
import AFTD.Kb.Physics.LorentzCoVectorBasisApply
import AFTD.Kb.Physics.LorentzCoVectorInstAddCommGroup
import AFTD.Kb.Physics.LorentzCoVectorInstFiniteDimensionalReal
import AFTD.Kb.Physics.LorentzCoVectorInstNorm
import AFTD.Kb.Physics.LorentzCoVectorIsNormedAddCommGroup
import AFTD.Kb.Physics.LorentzCoVectorIsNormedSpace
import AFTD.Kb.Physics.LorentzCoVectorInstInnerReal
import AFTD.Kb.Physics.LorentzCoVectorInnerProductSpace
import AFTD.Kb.Physics.LorentzCoVectorInstChartedSpace
import AFTD.Kb.Physics.LorentzCoVectorInstCoeFunForallSumFinOfNatNatReal

/-!
# Lorentz.CoVector.map_apply_eq_basis_mulVec

Topic: special_relativity   Node: 518751d01b38

Provenance: formalization of a published result. Source: Physlib, `Lorentz.CoVector.map_apply_eq_basis_mulVec`. Lean proof by Matteo Cipollina, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/CoVector/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lorentz.CoVector.map_apply_eq_basis_mulVec
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
open Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
open InnerProductSpace in
lemma Lorentz.CoVector.map_apply_eq_basis_mulVec {d : ℕ} (f : CoVector d →ₗ[ℝ] CoVector d) (p : CoVector d) :
    (f p) = (LinearMap.toMatrix basis basis) f *ᵥ p := by
  exact Eq.symm (LinearMap.toMatrix_mulVec_repr basis basis f p)
