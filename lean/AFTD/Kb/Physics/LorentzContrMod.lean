import AFTD.Prelude

/-!
# Lorentz.ContrMod

Topic: special_relativity   Node: 178d0e24022a

Provenance: formalization of a published result. Source: Physlib, `Lorentz.ContrMod`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/Vector/Pre/Modules.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The module for contravariant (up-index) real Lorentz vectors.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Module MatrixGroups Complex in
/-- The module for contravariant (up-index) real Lorentz vectors. -/
structure Lorentz.ContrMod (d : ℕ) where
  /-- The underlying value as a vector `Fin 1 ⊕ Fin d → ℝ`. -/
  val : Fin 1 ⊕ Fin d → ℝ
