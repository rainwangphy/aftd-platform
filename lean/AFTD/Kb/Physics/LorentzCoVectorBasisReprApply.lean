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
import AFTD.Kb.Physics.LorentzVectorBasis

/-!
# Lorentz.CoVector.basis_repr_apply

Topic: special_relativity   Node: e67b88ec0a74

Provenance: formalization of a published result. Source: Physlib, `Lorentz.CoVector.basis_repr_apply`. Lean proof by Matteo Cipollina, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/CoVector/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lorentz.CoVector.basis_repr_apply
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
open Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
open InnerProductSpace in
lemma Lorentz.CoVector.basis_repr_apply {d : ℕ} (p : CoVector d) (μ : Fin 1 ⊕ Fin d) :
    basis.repr p μ = p μ := by
  simp [basis]
  rw [Pi.basisFun_repr]
