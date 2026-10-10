import AFTD.Prelude

/-!
# Fermion.LeftHandedWeyl

Topic: special_relativity   Node: 4521e8fe20e0

Provenance: formalization of a published result. Source: Physlib, `Fermion.LeftHandedWeyl`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Weyl/LeftHanded.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The module in which left handed fermions live. This is equivalent to `Fin 2 → ℂ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The module in which left handed fermions live. This is equivalent to `Fin 2 → ℂ`. -/
structure Fermion.LeftHandedWeyl where
  /-- The underlying value in `Fin 2 → ℂ`. -/
  val : Fin 2 → ℂ
