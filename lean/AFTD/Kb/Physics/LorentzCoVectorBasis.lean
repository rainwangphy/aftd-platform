import AFTD.Prelude
import AFTD.Kb.Physics.LorentzCoVector
import AFTD.Kb.Physics.LorentzCoVectorInstAddCommMonoid
import AFTD.Kb.Physics.LorentzCoVectorInstModuleReal
import AFTD.Kb.Physics.LorentzCoVectorApplySmul
import AFTD.Kb.Physics.LorentzCoVectorApplyAdd
import AFTD.Kb.Physics.LorentzCoVectorApplySub
import AFTD.Kb.Physics.LorentzCoVectorApplySum
import AFTD.Kb.Physics.LorentzCoVectorNegApply
import AFTD.Kb.Physics.LorentzCoVectorZeroApply
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
# Lorentz.CoVector.basis

Topic: special_relativity   Node: fafaa64dc3d3

Provenance: formalization of a published result. Source: Physlib, `Lorentz.CoVector.basis`. Lean proof by Matteo Cipollina, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/CoVector/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The basis on `Vector d` indexed by `Fin 1 ⊕ Fin d`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
open Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
open InnerProductSpace in
/-- The basis on `Vector d` indexed by `Fin 1 ⊕ Fin d`. -/
noncomputable def Lorentz.CoVector.basis {d : ℕ} : Basis (Fin 1 ⊕ Fin d) ℝ (CoVector d) :=
  Pi.basisFun ℝ _
