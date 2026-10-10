import AFTD.Prelude

/-!
# IsSymmetric

Topic: classical_mechanics   Node: fbfdba9bbcc3

Provenance: formalization of a published result. Source: Physlib, `IsSymmetric`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A symmetric bilinear function.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A symmetric bilinear function. -/
class IsSymmetric {V : Type} [AddCommMonoid V] [Module ℚ V] (f : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) : Prop where
  swap : ∀ S T, f S T = f T S
