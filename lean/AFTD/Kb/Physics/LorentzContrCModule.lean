import AFTD.Prelude

/-!
# Lorentz.ContrℂModule

Topic: special_relativity   Node: c5ce6ca633e5

Provenance: formalization of a published result. Source: Physlib, `Lorentz.ContrℂModule`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/ComplexTensor/Vector/Pre/Modules.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The module for contravariant (up-index) complex Lorentz vectors.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open MatrixGroups in
open Complex in
/-- The module for contravariant (up-index) complex Lorentz vectors. -/
structure Lorentz.ContrℂModule where
  /-- The underlying value as a vector `Fin 1 ⊕ Fin 3 → ℂ`. -/
  val : Fin 1 ⊕ Fin 3 → ℂ
