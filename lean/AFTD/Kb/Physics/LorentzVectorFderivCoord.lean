import AFTD.Prelude
import AFTD.Kb.Physics.LorentzVector
import AFTD.Kb.Physics.LorentzVectorIsNormedAddCommGroup
import AFTD.Kb.Physics.LorentzVectorInstAddCommGroup
import AFTD.Kb.Physics.LorentzVectorInstModuleReal
import AFTD.Kb.Physics.LorentzVectorCoordCLM
import AFTD.Kb.Physics.LorentzVectorInstAddCommMonoid
import AFTD.Kb.Physics.LorentzVectorIsNormedSpace
import AFTD.Kb.Physics.LorentzVectorEquivEuclidApply
import AFTD.Kb.Physics.LorentzVectorAbsComponentLeNorm
import AFTD.Kb.Physics.LorentzVectorApplySmul
import AFTD.Kb.Physics.LorentzVectorApplyAdd
import AFTD.Kb.Physics.LorentzVectorApplySub
import AFTD.Kb.Physics.LorentzVectorNegApply
import AFTD.Kb.Physics.LorentzVectorZeroApply
import AFTD.Kb.Physics.LorentzVectorEquivPiApply
import AFTD.Kb.Physics.LorentzVectorInstFiniteDimensionalReal
import AFTD.Kb.Physics.LorentzVectorInstNorm
import AFTD.Kb.Physics.LorentzVectorInstInnerReal
import AFTD.Kb.Physics.LorentzVectorInnerProductSpace
import AFTD.Kb.Physics.LorentzVectorInstChartedSpace
import AFTD.Kb.Physics.LorentzVectorInstCoeFunForallSumFinOfNatNatReal

/-!
# Lorentz.Vector.fderiv_coord

Topic: special_relativity   Node: e2c38e951b88

Provenance: formalization of a published result. Source: Physlib, `Lorentz.Vector.fderiv_coord`. Lean proof by Matteo Cipollina, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/Vector/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lorentz.Vector.fderiv_coord
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
open Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
open InnerProductSpace in
@[simp]
lemma Lorentz.Vector.fderiv_coord {d : ℕ} (μ : Fin 1 ⊕ Fin d) (x : Vector d) :
    fderiv ℝ (fun v : Vector d => v μ) x = coordCLM μ := by
  change fderiv ℝ (coordCLM μ) x = coordCLM μ
  simp
