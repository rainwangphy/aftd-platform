import AFTD.Prelude

/-!
# HomogeneousQuadratic

Topic: classical_mechanics   Node: d6c051f3541f

Provenance: formalization of a published result. Source: Physlib, `HomogeneousQuadratic`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The structure defining a homogeneous quadratic equation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The structure defining a homogeneous quadratic equation. -/
@[simp]
def HomogeneousQuadratic (V : Type) [AddCommMonoid V] [Module ℚ V] : Type :=
  V →ₑ[((fun a => a ^ 2) : ℚ → ℚ)] ℚ
