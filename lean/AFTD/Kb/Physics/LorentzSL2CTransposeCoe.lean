import AFTD.Prelude

/-!
# Lorentz.SL2C.transpose_coe

Topic: special_relativity   Node: 83663e8a1dfa

Provenance: formalization of a published result. Source: Physlib, `Lorentz.SL2C.transpose_coe`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/SL2C/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lorentz.SL2C.transpose_coe
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module Matrix in
open MatrixGroups in
open Complex in
lemma Lorentz.SL2C.transpose_coe (M : SL(2, ℂ)) : M.1ᵀ = (M.transpose).1 := rfl
