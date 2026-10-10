import AFTD.Prelude
import AFTD.Kb.Physics.SULieAlgebra
import AFTD.Kb.Physics.SULieAlgebraSubmodule
import AFTD.Kb.Physics.SULieAlgebraInstBracket
import AFTD.Kb.Physics.SULieAlgebraValBracket
import AFTD.Kb.Physics.SULieAlgebraValOfMatrix
import AFTD.Kb.Physics.SULieAlgebraValConjApply

/-!
# SULieAlgebra.instLieRing

Topic: classical_mechanics   Node: 5000abf72289

Provenance: formalization of a published result. Source: Physlib, `SULieAlgebra.instLieRing`. Lean proof by Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Groups/SpecialUnitary/LieAlgebra/Basic.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`⁅x, y⁆ = i (x y - y x)` makes `SULieAlgebra n R` a Lie ring.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SULieAlgebra in
open Matrix TensorProduct ComplexStarModule in
variable {n : ℕ} {R : Type*} [CommRing R] [StarRing R] [Algebra ℝ R] [StarModule ℝ R] in
variable [Algebra ℂ R] [StarModule ℂ R] in
/-- `⁅x, y⁆ = i (x y - y x)` makes `SULieAlgebra n R` a Lie ring. -/
noncomputable instance SULieAlgebra.instLieRing : LieRing (SULieAlgebra n R) where
  add_lie x y z := Subtype.ext (by
    simp only [val_bracket, Submodule.coe_add, add_mul, mul_add, smul_add, smul_sub]
    abel)
  lie_add x y z := Subtype.ext (by
    simp only [val_bracket, Submodule.coe_add, add_mul, mul_add, smul_add, smul_sub]
    abel)
  lie_self x := Subtype.ext (by simp)
  leibniz_lie x y z := Subtype.ext (by
    simp only [val_bracket, Submodule.coe_add, mul_smul_comm, smul_mul_assoc, smul_smul,
      Complex.I_mul_I, smul_sub, mul_sub, sub_mul, mul_assoc]
    module)
