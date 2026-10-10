import AFTD.Prelude

/-!
# Lorentz.Vector

Topic: special_relativity   Node: 472115d809b7

Provenance: formalization of a published result. Source: Physlib, `Lorentz.Vector`. Lean proof by Matteo Cipollina, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/Vector/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Real contravariant Lorentz vector.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
open Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
/-- Real contravariant Lorentz vector. -/
@[implicit_reducible]
noncomputable def Lorentz.Vector (d : ℕ := 3) := Fin 1 ⊕ Fin d → ℝ

/- `Vector d` is applied directly as a function throughout the library. Marking it
  implicit-reducible lets such applications typecheck at implicit transparency, so that
  `rw` and `simp` can match patterns containing them (see the Lean 4.33 release notes on
  `backward.isDefEq.respectTransparency.types`). -/
