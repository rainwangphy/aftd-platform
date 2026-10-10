import AFTD.Prelude
import AFTD.Kb.Physics.SULieAlgebra
import AFTD.Kb.Physics.SULieAlgebraSubmodule
import AFTD.Kb.Physics.SULieAlgebraConj
import AFTD.Kb.Physics.SULieAlgebraInstBracket
import AFTD.Kb.Physics.SULieAlgebraValBracket
import AFTD.Kb.Physics.SULieAlgebraValConjApply
import AFTD.Kb.Physics.SULieAlgebraValOfMatrix
import AFTD.Kb.Physics.SULieAlgebraInstLieRing
import AFTD.Kb.Physics.SULieAlgebraInstLieAlgebraReal

/-!
# SULieAlgebra.conj_lie

Topic: classical_mechanics   Node: 6159a370f314

Provenance: formalization of a published result. Source: Physlib, `SULieAlgebra.conj_lie`. Lean proof by Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Groups/SpecialUnitary/LieAlgebra/Basic.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Conjugation by a unitary matrix preserves the bracket, so `conj` acts by Lie algebra automorphisms.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SULieAlgebra in
open Matrix TensorProduct ComplexStarModule in
variable {n : ℕ} {R : Type*} [CommRing R] [StarRing R] [Algebra ℝ R] [StarModule ℝ R] in
variable [Algebra ℂ R] [StarModule ℂ R] in
/-- Conjugation by a unitary matrix preserves the bracket, so `conj` acts by Lie algebra automorphisms. -/
lemma SULieAlgebra.conj_lie (U : unitaryGroup (Fin n) R) (x y : SULieAlgebra n R) :
    conj U ⁅x, y⁆ = ⁅conj U x, conj U y⁆ := by
  ext1
  simp only [val_conj_apply, val_bracket, Matrix.mul_smul, Matrix.smul_mul, mul_sub, sub_mul]
  congr 2 <;> simp only [mul_assoc, ← mul_assoc (star U.1) U.1, UnitaryGroup.star_mul_self,
    one_mul]
