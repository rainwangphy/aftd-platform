import AFTD.Prelude

/-!
# Lorentz.CoMod

Topic: special_relativity   Node: ec6b16e6ef0b

Provenance: formalization of a published result. Source: Physlib, `Lorentz.CoMod`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/Vector/Pre/Modules.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The module for covariant (up-index) complex Lorentz vectors.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Module MatrixGroups Complex in
/-- The module for covariant (up-index) complex Lorentz vectors. -/
structure Lorentz.CoMod (d : ℕ) where
  /-- The underlying value as a vector `Fin 1 ⊕ Fin d → ℝ`. -/
  val : Fin 1 ⊕ Fin d → ℝ
