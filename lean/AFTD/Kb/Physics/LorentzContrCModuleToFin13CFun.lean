import AFTD.Prelude
import AFTD.Kb.Physics.LorentzContrCModule

/-!
# Lorentz.ContrℂModule.toFin13ℂFun

Topic: special_relativity   Node: 072eb75e3c1c

Provenance: formalization of a published result. Source: Physlib, `Lorentz.ContrℂModule.toFin13ℂFun`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/ComplexTensor/Vector/Pre/Modules.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The equivalence between `ContrℂModule` and `Fin 1 ⊕ Fin 3 → ℂ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open MatrixGroups in
open Complex in
/-- The equivalence between `ContrℂModule` and `Fin 1 ⊕ Fin 3 → ℂ`. -/
noncomputable def Lorentz.ContrℂModule.toFin13ℂFun : ContrℂModule ≃ (Fin 1 ⊕ Fin 3 → ℂ) where
  toFun v := v.val
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl
