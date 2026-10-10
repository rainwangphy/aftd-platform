import AFTD.Prelude
import AFTD.Kb.Physics.LorentzVector
import AFTD.Kb.Physics.LorentzVectorInstAddCommMonoid
import AFTD.Kb.Physics.LorentzVectorInstAddCommGroup
import AFTD.Kb.Physics.LorentzVectorInstModuleReal
import AFTD.Kb.Physics.LorentzVectorBasis
import AFTD.Kb.Physics.LorentzVectorSumBasisEqZeroIff
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
import AFTD.Kb.Physics.LorentzVectorInstFiniteDimensionalReal
import AFTD.Kb.Physics.LorentzVectorInstNorm
import AFTD.Kb.Physics.LorentzVectorIsNormedAddCommGroup
import AFTD.Kb.Physics.LorentzVectorIsNormedSpace
import AFTD.Kb.Physics.LorentzVectorInstInnerReal
import AFTD.Kb.Physics.LorentzVectorInnerProductSpace
import AFTD.Kb.Physics.LorentzVectorInstChartedSpace
import AFTD.Kb.Physics.LorentzVectorInstCoeFunForallSumFinOfNatNatReal

/-!
# Lorentz.Vector.sum_inl_inr_basis_eq_zero_iff

Topic: special_relativity   Node: 987d4e0e30d1

Provenance: formalization of a published result. Source: Physlib, `Lorentz.Vector.sum_inl_inr_basis_eq_zero_iff`. Lean proof by Matteo Cipollina, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/Vector/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lorentz.Vector.sum_inl_inr_basis_eq_zero_iff
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
open Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
open InnerProductSpace in
lemma Lorentz.Vector.sum_inl_inr_basis_eq_zero_iff {d : ℕ} (f₀ : ℝ) (f : Fin d → ℝ) :
    f₀ • basis (Sum.inl 0) + (∑ i, f i • basis (Sum.inr i)) = 0 ↔
    f₀ = 0 ∧ ∀ i, f i = 0 := by
  let f' : Fin 1 ⊕ Fin d → ℝ := fun μ =>
    match μ with
    | Sum.inl 0 => f₀
    | Sum.inr i => f i
  have h1 : f₀ • basis (Sum.inl 0) + (∑ i, f i • basis (Sum.inr i))
    = ∑ μ, f' μ • basis μ := by simp [f']
  rw [h1, sum_basis_eq_zero_iff]
  simp [f']
