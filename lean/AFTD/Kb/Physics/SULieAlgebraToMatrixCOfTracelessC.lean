import AFTD.Prelude
import AFTD.Kb.Physics.SULieAlgebraComplexification
import AFTD.Kb.Physics.SULieAlgebra
import AFTD.Kb.Physics.SULieAlgebraSubmodule
import AFTD.Kb.Physics.SULieAlgebraToMatrixC
import AFTD.Kb.Physics.SULieAlgebraOfTracelessC
import AFTD.Kb.Physics.SULieAlgebraOfMatrix
import AFTD.Kb.Physics.SULieAlgebraToMatrixCTmul
import AFTD.Kb.Physics.SULieAlgebraValOfMatrix
import AFTD.Kb.Physics.SULieAlgebraValConjApply
import AFTD.Kb.Physics.SULieAlgebraValBracket
import AFTD.Kb.Physics.SULieAlgebraInstBracket
import AFTD.Kb.Physics.SULieAlgebraInstLieRing
import AFTD.Kb.Physics.SULieAlgebraInstLieAlgebraReal

/-!
# SULieAlgebra.toMatrixℂ_ofTracelessℂ

Topic: classical_mechanics   Node: d52b1724c3d3

Provenance: formalization of a published result. Source: Physlib, `SULieAlgebra.toMatrixℂ_ofTracelessℂ`. Lean proof by Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Groups/SpecialUnitary/LieAlgebra/Basic.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The matrix of `ofTracelessℂ M` is `M = ℜ M + i ℑ M`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SULieAlgebra in
open Matrix TensorProduct ComplexStarModule in
variable {n : ℕ} {R : Type*} [CommRing R] [StarRing R] [Algebra ℝ R] [StarModule ℝ R] in
variable [Algebra ℂ R] [StarModule ℂ R] in
/-- The matrix of `ofTracelessℂ M` is `M = ℜ M + i ℑ M`. -/
@[simp]
lemma SULieAlgebra.toMatrixℂ_ofTracelessℂ (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.trace = 0) :
    toMatrixℂ (ofTracelessℂ M hM) = M := by
  rw [ofTracelessℂ, map_add, toMatrixℂ_tmul, toMatrixℂ_tmul, one_smul, val_ofMatrix,
    val_ofMatrix, realPart_add_I_smul_imaginaryPart]
