import AFTD.Prelude
import AFTD.Kb.Physics.SULieAlgebra
import AFTD.Kb.Physics.SULieAlgebraSubmodule
import AFTD.Kb.Physics.SULieAlgebraStarValEq
import AFTD.Kb.Physics.SULieAlgebraOfMatrix
import AFTD.Kb.Physics.SULieAlgebraTraceValEqZero
import AFTD.Kb.Physics.SULieAlgebraValOfMatrix

/-!
# SULieAlgebra.conj

Topic: classical_mechanics   Node: 64ce6267e238

Provenance: formalization of a published result. Source: Physlib, `SULieAlgebra.conj`. Lean proof by Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Groups/SpecialUnitary/LieAlgebra/Basic.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The conjugation representation of the unitary group on `SULieAlgebra n R`: `x ↦ U x U†`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SULieAlgebra in
open Matrix TensorProduct ComplexStarModule in
variable {n : ℕ} {R : Type*} [CommRing R] [StarRing R] [Algebra ℝ R] [StarModule ℝ R] in
/-- The conjugation representation of the unitary group on `SULieAlgebra n R`: `x ↦ U x U†`. -/
noncomputable def SULieAlgebra.conj : Representation ℝ (unitaryGroup (Fin n) R) (SULieAlgebra n R) where
  toFun U :=
    { toFun x := ofMatrix (U.1 * x.1 * star U.1)
        (by rw [star_mul, star_mul, star_star, x.star_val_eq, mul_assoc])
        (by
          rw [Matrix.trace_mul_comm, ← mul_assoc, UnitaryGroup.star_mul_self U, one_mul,
            x.trace_val_eq_zero])
      map_add' x y := Subtype.ext (by simp [mul_add, add_mul])
      map_smul' r x := Subtype.ext (by simp) }
  map_one' := LinearMap.ext fun x => Subtype.ext (by simp)
  map_mul' U V := LinearMap.ext fun x => Subtype.ext (by simp [star_mul, mul_assoc])
