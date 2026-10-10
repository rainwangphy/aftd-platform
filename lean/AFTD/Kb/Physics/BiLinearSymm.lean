import AFTD.Prelude

/-!
# BiLinearSymm

Topic: classical_mechanics   Node: ee743fca22d8

Provenance: formalization of a published result. Source: Physlib, `BiLinearSymm`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The structure of a symmetric bilinear function.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The structure of a symmetric bilinear function. -/
structure BiLinearSymm (V : Type) [AddCommMonoid V] [Module ℚ V] extends V →ₗ[ℚ] V →ₗ[ℚ] ℚ where
  swap' : ∀ S T, toFun S T = toFun T S
