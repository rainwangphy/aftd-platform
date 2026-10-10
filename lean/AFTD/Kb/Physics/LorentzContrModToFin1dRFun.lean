import AFTD.Prelude
import AFTD.Kb.Physics.LorentzContrMod

/-!
# Lorentz.ContrMod.toFin1dℝFun

Topic: special_relativity   Node: 894105ae12b5

Provenance: formalization of a published result. Source: Physlib, `Lorentz.ContrMod.toFin1dℝFun`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/Vector/Pre/Modules.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The equivalence between `ContrMod` and `Fin 1 ⊕ Fin d → ℝ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Lorentz in
open Matrix Module MatrixGroups Complex in
variable {d : ℕ} in
/-- The equivalence between `ContrMod` and `Fin 1 ⊕ Fin d → ℝ`. -/
noncomputable def Lorentz.ContrMod.toFin1dℝFun : ContrMod d ≃ (Fin 1 ⊕ Fin d → ℝ) where
  toFun v := v.val
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl
