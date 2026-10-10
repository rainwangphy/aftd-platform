import AFTD.Prelude

/-!
# Lorentz.CoVector

Topic: special_relativity   Node: 52899bd266fb

Provenance: formalization of a published result. Source: Physlib, `Lorentz.CoVector`. Lean proof by Matteo Cipollina, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/CoVector/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Real covariant Lorentz vector.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
open Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
/-- Real covariant Lorentz vector. -/
@[implicit_reducible]
noncomputable def Lorentz.CoVector (d : ℕ := 3) := Fin 1 ⊕ Fin d → ℝ

/- As for `Vector`, `CoVector d` is applied directly as a function throughout the library;
  marking it implicit-reducible lets such applications typecheck at implicit transparency. -/
