import AFTD.Prelude
import AFTD.Kb.Physics.SULieAlgebra
import AFTD.Kb.Physics.SULieAlgebraComplexification
import AFTD.Kb.Physics.SULieAlgebraSubmodule
import AFTD.Kb.Physics.SULieAlgebraToMatrixC
import AFTD.Kb.Physics.SULieAlgebraValOfMatrix
import AFTD.Kb.Physics.SULieAlgebraValConjApply
import AFTD.Kb.Physics.SULieAlgebraValBracket
import AFTD.Kb.Physics.SULieAlgebraInstBracket
import AFTD.Kb.Physics.SULieAlgebraInstLieRing
import AFTD.Kb.Physics.SULieAlgebraInstLieAlgebraReal

/-!
# SULieAlgebra.toMatrixℂ_tmul

Topic: classical_mechanics   Node: 6eb3687c0e9e

Provenance: formalization of a published result. Source: Physlib, `SULieAlgebra.toMatrixℂ_tmul`. Lean proof by Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Groups/SpecialUnitary/LieAlgebra/Basic.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SULieAlgebra.toMatrixℂ_tmul
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SULieAlgebra in
open Matrix TensorProduct ComplexStarModule in
variable {n : ℕ} {R : Type*} [CommRing R] [StarRing R] [Algebra ℝ R] [StarModule ℝ R] in
variable [Algebra ℂ R] [StarModule ℂ R] in
@[simp]
lemma SULieAlgebra.toMatrixℂ_tmul (z : ℂ) (x : SULieAlgebra n ℂ) : toMatrixℂ (z ⊗ₜ x) = z • x.1 := rfl
