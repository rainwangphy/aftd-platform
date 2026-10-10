import AFTD.Prelude
import AFTD.Kb.Physics.SULieAlgebra
import AFTD.Kb.Physics.SULieAlgebraSubmodule
import AFTD.Kb.Physics.SULieAlgebraInstLieRing
import AFTD.Kb.Physics.SULieAlgebraValBracket
import AFTD.Kb.Physics.SULieAlgebraValOfMatrix
import AFTD.Kb.Physics.SULieAlgebraValConjApply
import AFTD.Kb.Physics.SULieAlgebraInstBracket

/-!
# SULieAlgebra.instLieAlgebraReal

Topic: classical_mechanics   Node: 2343f7c9cd6c

Provenance: formalization of a published result. Source: Physlib, `SULieAlgebra.instLieAlgebraReal`. Lean proof by Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Groups/SpecialUnitary/LieAlgebra/Basic.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The bracket is `ℝ`-bilinear, so `SULieAlgebra n R` is a real Lie algebra.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SULieAlgebra in
open Matrix TensorProduct ComplexStarModule in
variable {n : ℕ} {R : Type*} [CommRing R] [StarRing R] [Algebra ℝ R] [StarModule ℝ R] in
variable [Algebra ℂ R] [StarModule ℂ R] in
/-- The bracket is `ℝ`-bilinear, so `SULieAlgebra n R` is a real Lie algebra. -/
noncomputable instance SULieAlgebra.instLieAlgebraReal : LieAlgebra ℝ (SULieAlgebra n R) where
  lie_smul r x y := Subtype.ext (by
    ext i j
    simp only [val_bracket, Submodule.coe_smul, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.mul_apply]
    simp only [Algebra.smul_def, mul_sub, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun k _ => by ring)
