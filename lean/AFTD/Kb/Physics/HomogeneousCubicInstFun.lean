import AFTD.Prelude
import AFTD.Kb.Physics.HomogeneousCubic

/-!
# HomogeneousCubic.instFun

Topic: classical_mechanics   Node: 79df736a8e22

Provenance: formalization of a published result. Source: Physlib, `HomogeneousCubic.instFun`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A homogeneous cubic equation can be treated as a function from `V` to `ℚ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {V : Type} [AddCommMonoid V] [Module ℚ V] in
/-- A homogeneous cubic equation can be treated as a function from `V` to `ℚ`. -/
instance HomogeneousCubic.instFun : FunLike (HomogeneousCubic V) V ℚ where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    simp_all
