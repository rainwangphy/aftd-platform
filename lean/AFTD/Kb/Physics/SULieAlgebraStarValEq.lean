import AFTD.Prelude
import AFTD.Kb.Physics.SULieAlgebra
import AFTD.Kb.Physics.SULieAlgebraSubmodule
import AFTD.Kb.Physics.SULieAlgebraValOfMatrix

/-!
# SULieAlgebra.star_val_eq

Topic: classical_mechanics   Node: 3af7a557958f

Provenance: formalization of a published result. Source: Physlib, `SULieAlgebra.star_val_eq`. Lean proof by Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Groups/SpecialUnitary/LieAlgebra/Basic.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The underlying matrix of an element is hermitian.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SULieAlgebra in
open Matrix TensorProduct ComplexStarModule in
variable {n : ℕ} {R : Type*} [CommRing R] [StarRing R] [Algebra ℝ R] [StarModule ℝ R] in
/-- The underlying matrix of an element is hermitian. -/
lemma SULieAlgebra.star_val_eq (x : SULieAlgebra n R) : star x.1 = x.1 := x.2.1
