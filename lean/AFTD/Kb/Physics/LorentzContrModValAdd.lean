import AFTD.Prelude
import AFTD.Kb.Physics.LorentzContrMod
import AFTD.Kb.Physics.LorentzContrModInstAddCommGroup

/-!
# Lorentz.ContrMod.val_add

Topic: special_relativity   Node: ae18fea9d917

Provenance: formalization of a published result. Source: Physlib, `Lorentz.ContrMod.val_add`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/Vector/Pre/Modules.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lorentz.ContrMod.val_add
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Lorentz Lorentz.ContrMod in
open Matrix Module MatrixGroups Complex in
variable {d : ℕ} in
@[simp]
lemma Lorentz.ContrMod.val_add (ψ ψ' : ContrMod d) : (ψ + ψ').val = ψ.val + ψ'.val := rfl
