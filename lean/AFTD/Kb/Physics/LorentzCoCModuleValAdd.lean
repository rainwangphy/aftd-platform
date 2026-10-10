import AFTD.Prelude
import AFTD.Kb.Physics.LorentzCoCModule
import AFTD.Kb.Physics.LorentzCoCModuleInstAddCommMonoid

/-!
# Lorentz.CoℂModule.val_add

Topic: special_relativity   Node: 612f167f3467

Provenance: formalization of a published result. Source: Physlib, `Lorentz.CoℂModule.val_add`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/ComplexTensor/Vector/Pre/Modules.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lorentz.CoℂModule.val_add
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open MatrixGroups in
open Complex in
@[simp]
lemma Lorentz.CoℂModule.val_add (ψ ψ' : CoℂModule) : (ψ + ψ').val = ψ.val + ψ'.val := rfl
