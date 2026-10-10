import AFTD.Prelude
import AFTD.Kb.Physics.SULieAlgebra
import AFTD.Kb.Physics.SULieAlgebraSubmodule
import AFTD.Kb.Physics.SULieAlgebraConj
import AFTD.Kb.Physics.SULieAlgebraValOfMatrix

/-!
# SULieAlgebra.val_conj_apply

Topic: classical_mechanics   Node: b06537cfd55d

Provenance: formalization of a published result. Source: Physlib, `SULieAlgebra.val_conj_apply`. Lean proof by Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Groups/SpecialUnitary/LieAlgebra/Basic.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The underlying matrix of `conj U x` is `U x U†`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SULieAlgebra in
open Matrix TensorProduct ComplexStarModule in
variable {n : ℕ} {R : Type*} [CommRing R] [StarRing R] [Algebra ℝ R] [StarModule ℝ R] in
/-- The underlying matrix of `conj U x` is `U x U†`. -/
@[simp]
lemma SULieAlgebra.val_conj_apply (U : unitaryGroup (Fin n) R) (x : SULieAlgebra n R) :
    (conj U x).1 = U.1 * x.1 * star U.1 := rfl
