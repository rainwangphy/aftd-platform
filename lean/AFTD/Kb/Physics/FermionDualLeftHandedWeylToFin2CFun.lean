import AFTD.Prelude
import AFTD.Kb.Physics.FermionDualLeftHandedWeyl

/-!
# Fermion.DualLeftHandedWeyl.toFin2ℂFun

Topic: special_relativity   Node: a8bdebe4e8a9

Provenance: formalization of a published result. Source: Physlib, `Fermion.DualLeftHandedWeyl.toFin2ℂFun`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Weyl/DualLeftHanded.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The equivalence between `DualLeftHandedWeyl` and `Fin 2 → ℂ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
/-- The equivalence between `DualLeftHandedWeyl` and `Fin 2 → ℂ`. -/
noncomputable def Fermion.DualLeftHandedWeyl.toFin2ℂFun : DualLeftHandedWeyl ≃ (Fin 2 → ℂ) where
  toFun v := v.val
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl
