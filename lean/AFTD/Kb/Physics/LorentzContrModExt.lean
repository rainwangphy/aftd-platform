import AFTD.Prelude
import AFTD.Kb.Physics.LorentzContrMod

/-!
# Lorentz.ContrMod.ext

Topic: special_relativity   Node: 1dd0024c4820

Provenance: formalization of a published result. Source: Physlib, `Lorentz.ContrMod.ext`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/Vector/Pre/Modules.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lorentz.ContrMod.ext
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Lorentz in
open Matrix Module MatrixGroups Complex in
variable {d : ℕ} in
@[ext]
lemma Lorentz.ContrMod.ext {ψ ψ' : ContrMod d} (h : ψ.val = ψ'.val) : ψ = ψ' := by
  cases ψ
  cases ψ'
  subst h
  rfl
