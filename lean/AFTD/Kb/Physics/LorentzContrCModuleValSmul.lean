import AFTD.Prelude
import AFTD.Kb.Physics.LorentzContrCModule
import AFTD.Kb.Physics.LorentzContrCModuleInstAddCommGroup
import AFTD.Kb.Physics.LorentzContrCModuleInstAddCommMonoid
import AFTD.Kb.Physics.LorentzContrCModuleInstModuleComplex
import AFTD.Kb.Physics.LorentzContrCModuleValAdd

/-!
# Lorentz.ContrℂModule.val_smul

Topic: special_relativity   Node: 6fc16d4805d1

Provenance: formalization of a published result. Source: Physlib, `Lorentz.ContrℂModule.val_smul`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/ComplexTensor/Vector/Pre/Modules.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lorentz.ContrℂModule.val_smul
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open MatrixGroups in
open Complex in
@[simp]
lemma Lorentz.ContrℂModule.val_smul (r : ℂ) (ψ : ContrℂModule) : (r • ψ).val = r • ψ.val := rfl
