import AFTD.Prelude
import AFTD.Kb.Physics.SULieAlgebraComplexification
import AFTD.Kb.Physics.SULieAlgebraOfTracelessC
import AFTD.Kb.Physics.SULieAlgebra
import AFTD.Kb.Physics.SULieAlgebraSubmodule
import AFTD.Kb.Physics.SULieAlgebraOfMatrix
import AFTD.Kb.Physics.SULieAlgebraValOfMatrix
import AFTD.Kb.Physics.SULieAlgebraValConjApply
import AFTD.Kb.Physics.SULieAlgebraValBracket
import AFTD.Kb.Physics.SULieAlgebraToMatrixCTmul
import AFTD.Kb.Physics.SULieAlgebraToMatrixCOfTracelessC
import AFTD.Kb.Physics.SULieAlgebraInstBracket
import AFTD.Kb.Physics.SULieAlgebraInstLieRing
import AFTD.Kb.Physics.SULieAlgebraInstLieAlgebraReal

/-!
# SULieAlgebra.ofTracelessℂ_add

Topic: classical_mechanics   Node: 7efdd6ee1d73

Provenance: formalization of a published result. Source: Physlib, `SULieAlgebra.ofTracelessℂ_add`. Lean proof by Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Groups/SpecialUnitary/LieAlgebra/Basic.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`ofTracelessℂ` is additive.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SULieAlgebra in
open Matrix TensorProduct ComplexStarModule in
variable {n : ℕ} {R : Type*} [CommRing R] [StarRing R] [Algebra ℝ R] [StarModule ℝ R] in
variable [Algebra ℂ R] [StarModule ℂ R] in
/-- `ofTracelessℂ` is additive. -/
lemma SULieAlgebra.ofTracelessℂ_add (M N : Matrix (Fin n) (Fin n) ℂ) (hM : M.trace = 0) (hN : N.trace = 0)
    (hMN : (M + N).trace = 0) :
    ofTracelessℂ (M + N) hMN = ofTracelessℂ M hM + ofTracelessℂ N hN := by
  rw [ofTracelessℂ, ofTracelessℂ, ofTracelessℂ, add_add_add_comm, ← tmul_add, ← tmul_add]
  congr 2 <;> exact Subtype.ext (by simp)
