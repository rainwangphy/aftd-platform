import AFTD.Prelude
import AFTD.Kb.Physics.BiLinearSymm

/-!
# BiLinearSymm.instFun

Topic: classical_mechanics   Node: aefdfbb582f4

Provenance: formalization of a published result. Source: Physlib, `BiLinearSymm.instFun`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A symmetric bilinear form can be treated as a function from `V` to `V →ₗ[ℚ] ℚ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators in
variable {V : Type} [AddCommMonoid V] [Module ℚ V] in
/-- A symmetric bilinear form can be treated as a function from `V` to `V →ₗ[ℚ] ℚ`. -/
instance BiLinearSymm.instFun (V : Type) [AddCommMonoid V] [Module ℚ V] :
    FunLike (BiLinearSymm V) V (V →ₗ[ℚ] ℚ) where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    simp_all
