import AFTD.Prelude
import AFTD.Kb.Physics.LorentzContrMod
import AFTD.Kb.Physics.LorentzContrModInstAddCommGroup
import AFTD.Kb.Physics.LorentzContrModInstModuleReal
import AFTD.Kb.Physics.LorentzContrModValAdd

/-!
# Lorentz.ContrMod.val_smul

Topic: special_relativity   Node: f949898c71ac

Provenance: formalization of a published result. Source: Physlib, `Lorentz.ContrMod.val_smul`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/Vector/Pre/Modules.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lorentz.ContrMod.val_smul
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Lorentz Lorentz.ContrMod in
open Matrix Module MatrixGroups Complex in
variable {d : ℕ} in
@[simp]
lemma Lorentz.ContrMod.val_smul (r : ℝ) (ψ : ContrMod d) : (r • ψ).val = r • ψ.val := rfl
