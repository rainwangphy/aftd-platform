import AFTD.Prelude
import AFTD.Kb.Physics.TriLinearSymm
import AFTD.Kb.Physics.BiLinearSymmInstFun

/-!
# TriLinearSymm.instFun

Topic: classical_mechanics   Node: 9b9509bac585

Provenance: formalization of a published result. Source: Physlib, `TriLinearSymm.instFun`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A symmetric trilinear form can be treated as a function from `V` to `V →ₗ[ℚ] V →ₗ[ℚ] ℚ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators in
variable {V : Type} [AddCommMonoid V] [Module ℚ V] in
/-- A symmetric trilinear form can be treated as a function from `V` to `V →ₗ[ℚ] V →ₗ[ℚ] ℚ`. -/
instance TriLinearSymm.instFun : FunLike (TriLinearSymm V) V (V →ₗ[ℚ] V →ₗ[ℚ] ℚ) where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    simp_all
