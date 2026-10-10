import AFTD.Prelude
import AFTD.Kb.Physics.LorentzContrCModule
import AFTD.Kb.Physics.LorentzContrCModuleInstAddCommMonoid
import AFTD.Kb.Physics.LorentzContrCModuleToFin13CFun

/-!
# Lorentz.ContrℂModule.toFin13ℂAddEquiv

Topic: special_relativity   Node: 1a35fe61df7c

Provenance: formalization of a published result. Source: Physlib, `Lorentz.ContrℂModule.toFin13ℂAddEquiv`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/ComplexTensor/Vector/Pre/Modules.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The additive equivalence between `ContrℂModule` and `Fin 1 ⊕ Fin 3 → ℂ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open MatrixGroups in
open Complex in
/-- The additive equivalence between `ContrℂModule` and `Fin 1 ⊕ Fin 3 → ℂ`. -/
noncomputable def Lorentz.ContrℂModule.toFin13ℂAddEquiv : ContrℂModule ≃+ (Fin 1 ⊕ Fin 3 → ℂ) :=
  { toFin13ℂFun with map_add' _ _ := rfl }
