import AFTD.Prelude
import AFTD.Kb.Physics.SULieAlgebraSubmodule

/-!
# SULieAlgebra

Topic: classical_mechanics   Node: b6b16d81167e

Provenance: formalization of a published result. Source: Physlib, `SULieAlgebra`. Lean proof by Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Groups/SpecialUnitary/LieAlgebra/Basic.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Traceless hermitian `n × n` matrices with entries in `R`, as a real Lie algebra; `SULieAlgebra n ℂ` is `su(n)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix TensorProduct ComplexStarModule in
/-- Traceless hermitian `n × n` matrices with entries in `R`, as a real Lie algebra; `SULieAlgebra n ℂ` is `su(n)`. -/
abbrev SULieAlgebra (n : ℕ) (R : Type*) [CommRing R] [StarRing R] [Algebra ℝ R]
    [StarModule ℝ R] : Type _ :=
  ↥(SULieAlgebra.submodule n R)
