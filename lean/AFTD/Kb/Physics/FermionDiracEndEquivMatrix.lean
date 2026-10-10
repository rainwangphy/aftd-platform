import AFTD.Prelude
import AFTD.Kb.Physics.FermionDirac
import AFTD.Kb.Physics.FermionDiracInstAddCommGroup
import AFTD.Kb.Physics.FermionDiracInstModuleComplex
import AFTD.Kb.Physics.FermionDiracChiralBasis
import AFTD.Kb.Physics.FermionDiracLeftAdd
import AFTD.Kb.Physics.FermionDiracDualRightAdd
import AFTD.Kb.Physics.FermionDiracLeftSmul
import AFTD.Kb.Physics.FermionDiracDualRightSmul

/-!
# Fermion.Dirac.endEquivMatrix

Topic: special_relativity   Node: 0cda11a07b71

Provenance: formalization of a published result. Source: Physlib, `Fermion.Dirac.endEquivMatrix`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Dirac/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Dirac endomorphisms as matrices in the Dirac representation. The change of coordinates from the chiral representation is `S = [1, 1; -1, 1]`, with `2 × 2` blocks, so this map sends `f` to `S [f] S⁻¹`. The common normalization factor `1 / √2` cancels in conjugation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
open Module in
/-- Dirac endomorphisms as matrices in the Dirac representation. The change of coordinates from the chiral representation is `S = [1, 1; -1, 1]`, with `2 × 2` blocks, so this map sends `f` to `S [f] S⁻¹`. The common normalization factor `1 / √2` cancels in conjugation. -/
noncomputable def Fermion.Dirac.endEquivMatrix : Module.End ℂ Dirac ≃ₐ[ℂ] Matrix (Fin 4) (Fin 4) ℂ :=
  (LinearEquiv.conjAlgEquiv ℂ
    (Matrix.toLinOfInv chiralBasis chiralBasis
      (M := !![1, 0, 1, 0; 0, 1, 0, 1; -1, 0, 1, 0; 0, -1, 0, 1])
      (M' := (2 : ℂ)⁻¹ • !![1, 0, -1, 0; 0, 1, 0, -1; 1, 0, 1, 0; 0, 1, 0, 1])
      (by ext i j; fin_cases i <;> fin_cases j <;>
          norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.one_apply])
      (by ext i j; fin_cases i <;> fin_cases j <;>
          norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.one_apply]))).trans
    (LinearMap.toMatrixAlgEquiv chiralBasis)
