import AFTD.Prelude
import AFTD.Kb.Physics.LorentzContrCModule

/-!
# Lorentz.ContrℂModule.ext

Topic: special_relativity   Node: 931b8dcaaa1c

Provenance: formalization of a published result. Source: Physlib, `Lorentz.ContrℂModule.ext`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/ComplexTensor/Vector/Pre/Modules.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lorentz.ContrℂModule.ext
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open MatrixGroups in
open Complex in
@[ext]
lemma Lorentz.ContrℂModule.ext (ψ ψ' : ContrℂModule) (h : ψ.val = ψ'.val) : ψ = ψ' := by
  cases ψ
  cases ψ'
  subst h
  rfl
