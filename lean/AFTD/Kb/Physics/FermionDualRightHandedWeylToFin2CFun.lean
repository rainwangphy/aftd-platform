import AFTD.Prelude
import AFTD.Kb.Physics.FermionDualRightHandedWeyl

/-!
# Fermion.DualRightHandedWeyl.toFin2ℂFun

Topic: special_relativity   Node: 2cd48257d7c0

Provenance: formalization of a published result. Source: Physlib, `Fermion.DualRightHandedWeyl.toFin2ℂFun`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Weyl/DualRightHanded.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The equivalence between `DualRightHandedWeyl` and `Fin 2 → ℂ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
/-- The equivalence between `DualRightHandedWeyl` and `Fin 2 → ℂ`. -/
noncomputable def Fermion.DualRightHandedWeyl.toFin2ℂFun : DualRightHandedWeyl ≃ (Fin 2 → ℂ) where
  toFun v := v.val
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl
