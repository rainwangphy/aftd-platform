import AFTD.Prelude
import AFTD.Kb.Physics.SULieAlgebra
import AFTD.Kb.Physics.SULieAlgebraSubmodule
import AFTD.Kb.Physics.SULieAlgebraStarValEq
import AFTD.Kb.Physics.SULieAlgebraOfMatrix
import AFTD.Kb.Physics.SULieAlgebraValOfMatrix
import AFTD.Kb.Physics.SULieAlgebraValConjApply

/-!
# SULieAlgebra.instBracket

Topic: classical_mechanics   Node: 158cdce7ddfe

Provenance: formalization of a published result. Source: Physlib, `SULieAlgebra.instBracket`. Lean proof by Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Groups/SpecialUnitary/LieAlgebra/Basic.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The bracket `⁅x, y⁆ = i (x y - y x)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SULieAlgebra in
open Matrix TensorProduct ComplexStarModule in
variable {n : ℕ} {R : Type*} [CommRing R] [StarRing R] [Algebra ℝ R] [StarModule ℝ R] in
variable [Algebra ℂ R] [StarModule ℂ R] in
/-- The bracket `⁅x, y⁆ = i (x y - y x)`. -/
noncomputable instance SULieAlgebra.instBracket : Bracket (SULieAlgebra n R) (SULieAlgebra n R) where
  bracket x y := ofMatrix (Complex.I • (x.1 * y.1 - y.1 * x.1))
    (by
      rw [star_smul, star_sub, star_mul, star_mul, x.star_val_eq, y.star_val_eq,
        Complex.star_def, Complex.conj_I, neg_smul, ← smul_neg, neg_sub])
    (by rw [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self, smul_zero])
