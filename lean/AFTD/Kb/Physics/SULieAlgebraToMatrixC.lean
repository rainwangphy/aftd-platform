import AFTD.Prelude
import AFTD.Kb.Physics.SULieAlgebraComplexification
import AFTD.Kb.Physics.SULieAlgebra
import AFTD.Kb.Physics.SULieAlgebraSubmodule
import AFTD.Kb.Physics.SULieAlgebraValOfMatrix
import AFTD.Kb.Physics.SULieAlgebraValConjApply
import AFTD.Kb.Physics.SULieAlgebraValBracket
import AFTD.Kb.Physics.SULieAlgebraInstBracket
import AFTD.Kb.Physics.SULieAlgebraInstLieRing
import AFTD.Kb.Physics.SULieAlgebraInstLieAlgebraReal

/-!
# SULieAlgebra.toMatrixℂ

Topic: classical_mechanics   Node: 08768e5d3946

Provenance: formalization of a published result. Source: Physlib, `SULieAlgebra.toMatrixℂ`. Lean proof by Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Groups/SpecialUnitary/LieAlgebra/Basic.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The underlying matrix of an element of the complexification, `z ⊗ x ↦ z x`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SULieAlgebra in
open Matrix TensorProduct ComplexStarModule in
variable {n : ℕ} {R : Type*} [CommRing R] [StarRing R] [Algebra ℝ R] [StarModule ℝ R] in
variable [Algebra ℂ R] [StarModule ℂ R] in
/-- The underlying matrix of an element of the complexification, `z ⊗ x ↦ z x`. -/
noncomputable def SULieAlgebra.toMatrixℂ : Complexification n →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  (SULieAlgebra.submodule n ℂ).subtype.liftBaseChange ℂ
