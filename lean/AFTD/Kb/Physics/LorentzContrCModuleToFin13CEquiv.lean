import AFTD.Prelude
import AFTD.Kb.Physics.LorentzContrCModule
import AFTD.Kb.Physics.LorentzContrCModuleInstAddCommMonoid
import AFTD.Kb.Physics.LorentzContrCModuleInstModuleComplex
import AFTD.Kb.Physics.LorentzContrCModuleToFin13CAddEquiv
import AFTD.Kb.Physics.LorentzContrCModuleValAdd
import AFTD.Kb.Physics.LorentzContrCModuleValSmul

/-!
# Lorentz.ContrℂModule.toFin13ℂEquiv

Topic: special_relativity   Node: 8e0a33031467

Provenance: formalization of a published result. Source: Physlib, `Lorentz.ContrℂModule.toFin13ℂEquiv`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/ComplexTensor/Vector/Pre/Modules.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The linear equivalence between `ContrℂModule` and `(Fin 1 ⊕ Fin 3 → ℂ)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open MatrixGroups in
open Complex in
/-- The linear equivalence between `ContrℂModule` and `(Fin 1 ⊕ Fin 3 → ℂ)`. -/
@[simps!]
noncomputable def Lorentz.ContrℂModule.toFin13ℂEquiv : ContrℂModule ≃ₗ[ℂ] (Fin 1 ⊕ Fin 3 → ℂ) :=
  AddEquiv.linearEquiv ℂ toFin13ℂAddEquiv
