import AFTD.Prelude

/-!
# HomogeneousCubic

Topic: classical_mechanics   Node: 0653122445c1

Provenance: formalization of a published result. Source: Physlib, `HomogeneousCubic`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The structure of a homogeneous cubic equation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The structure of a homogeneous cubic equation. -/
@[simp]
def HomogeneousCubic (V : Type) [AddCommMonoid V] [Module ℚ V] : Type :=
  V →ₑ[((fun a => a ^ 3) : ℚ → ℚ)] ℚ
