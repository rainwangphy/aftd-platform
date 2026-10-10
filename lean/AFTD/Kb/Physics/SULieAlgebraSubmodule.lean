import AFTD.Prelude

/-!
# SULieAlgebra.submodule

Topic: classical_mechanics   Node: d749b56de08e

Provenance: formalization of a published result. Source: Physlib, `SULieAlgebra.submodule`. Lean proof by Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Groups/SpecialUnitary/LieAlgebra/Basic.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The traceless hermitian `n × n` matrices with entries in `R`, as a real subspace.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix TensorProduct ComplexStarModule in
/-- The traceless hermitian `n × n` matrices with entries in `R`, as a real subspace. -/
abbrev SULieAlgebra.submodule (n : ℕ) (R : Type*) [CommRing R] [StarRing R] [Algebra ℝ R]
    [StarModule ℝ R] : Submodule ℝ (Matrix (Fin n) (Fin n) R) :=
  selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) R) ⊓
    LinearMap.ker (Matrix.traceLinearMap (Fin n) ℝ R)
