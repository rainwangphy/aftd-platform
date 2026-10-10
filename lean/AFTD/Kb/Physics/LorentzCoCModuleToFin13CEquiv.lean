import AFTD.Prelude
import AFTD.Kb.Physics.LorentzCoCModule
import AFTD.Kb.Physics.LorentzCoCModuleInstAddCommMonoid
import AFTD.Kb.Physics.LorentzCoCModuleInstModuleComplex
import AFTD.Kb.Physics.LorentzCoCModuleToFin13CAddEquiv
import AFTD.Kb.Physics.LorentzCoCModuleValAdd
import AFTD.Kb.Physics.LorentzCoCModuleValSmul

/-!
# Lorentz.CoℂModule.toFin13ℂEquiv

Topic: special_relativity   Node: 73eb08dd8bed

Provenance: formalization of a published result. Source: Physlib, `Lorentz.CoℂModule.toFin13ℂEquiv`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/ComplexTensor/Vector/Pre/Modules.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The linear equivalence between `CoℂModule` and `(Fin 1 ⊕ Fin 3 → ℂ)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open MatrixGroups in
open Complex in
/-- The linear equivalence between `CoℂModule` and `(Fin 1 ⊕ Fin 3 → ℂ)`. -/
@[simps!]
noncomputable def Lorentz.CoℂModule.toFin13ℂEquiv : CoℂModule ≃ₗ[ℂ] (Fin 1 ⊕ Fin 3 → ℂ) :=
  AddEquiv.linearEquiv ℂ toFin13ℂAddEquiv
