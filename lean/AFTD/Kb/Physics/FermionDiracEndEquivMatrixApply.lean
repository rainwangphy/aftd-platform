import AFTD.Prelude
import AFTD.Kb.Physics.FermionDirac
import AFTD.Kb.Physics.FermionDiracInstAddCommGroup
import AFTD.Kb.Physics.FermionDiracInstModuleComplex
import AFTD.Kb.Physics.FermionDiracEndEquivMatrix
import AFTD.Kb.Physics.FermionDiracChiralBasis
import AFTD.Kb.Physics.FermionDiracLeftAdd
import AFTD.Kb.Physics.FermionDiracDualRightAdd
import AFTD.Kb.Physics.FermionDiracLeftSmul
import AFTD.Kb.Physics.FermionDiracDualRightSmul

/-!
# Fermion.Dirac.endEquivMatrix_apply

Topic: special_relativity   Node: 383e836c4d7b

Provenance: formalization of a published result. Source: Physlib, `Fermion.Dirac.endEquivMatrix_apply`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Dirac/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The change of coordinates from the chiral representation to the Dirac representation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
open Module in
/-- The change of coordinates from the chiral representation to the Dirac representation. -/
lemma Fermion.Dirac.endEquivMatrix_apply (f : Module.End ℂ Dirac) :
    endEquivMatrix f =
      !![1, 0, 1, 0; 0, 1, 0, 1; -1, 0, 1, 0; 0, -1, 0, 1] *
        LinearMap.toMatrix chiralBasis chiralBasis f *
        ((2 : ℂ)⁻¹ • !![1, 0, -1, 0; 0, 1, 0, -1; 1, 0, 1, 0; 0, 1, 0, 1]) := by
  simp only [endEquivMatrix, AlgEquiv.trans_apply, LinearEquiv.conjAlgEquiv_apply,
    LinearMap.toMatrixAlgEquiv, AlgEquiv.ofLinearEquiv_apply]
  simp only [Matrix.toLinOfInv, LinearEquiv.symm_mk]
  simp only [LinearMap.toMatrix_comp chiralBasis chiralBasis chiralBasis,
    Matrix.mul_assoc]
  apply congrArg₂ (· * ·)
  · exact LinearMap.toMatrix_toLin chiralBasis chiralBasis _
  · apply congrArg _
    exact LinearMap.toMatrix_toLin chiralBasis chiralBasis _
