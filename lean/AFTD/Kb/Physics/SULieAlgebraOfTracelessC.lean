import AFTD.Prelude
import AFTD.Kb.Physics.SULieAlgebraComplexification
import AFTD.Kb.Physics.SULieAlgebra
import AFTD.Kb.Physics.SULieAlgebraSubmodule
import AFTD.Kb.Physics.SULieAlgebraOfMatrix
import AFTD.Kb.Physics.SULieAlgebraValOfMatrix
import AFTD.Kb.Physics.SULieAlgebraValConjApply
import AFTD.Kb.Physics.SULieAlgebraValBracket
import AFTD.Kb.Physics.SULieAlgebraToMatrixCTmul
import AFTD.Kb.Physics.SULieAlgebraInstBracket
import AFTD.Kb.Physics.SULieAlgebraInstLieRing
import AFTD.Kb.Physics.SULieAlgebraInstLieAlgebraReal

/-!
# SULieAlgebra.ofTracelessℂ

Topic: classical_mechanics   Node: e3542454a2a0

Provenance: formalization of a published result. Source: Physlib, `SULieAlgebra.ofTracelessℂ`. Lean proof by Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Groups/SpecialUnitary/LieAlgebra/Basic.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The element `1 ⊗ ℜ M + i ⊗ ℑ M` of the complexification with the traceless matrix `M`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SULieAlgebra in
open Matrix TensorProduct ComplexStarModule in
variable {n : ℕ} {R : Type*} [CommRing R] [StarRing R] [Algebra ℝ R] [StarModule ℝ R] in
variable [Algebra ℂ R] [StarModule ℂ R] in
/-- The element `1 ⊗ ℜ M + i ⊗ ℑ M` of the complexification with the traceless matrix `M`. -/
noncomputable def SULieAlgebra.ofTracelessℂ (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.trace = 0) :
    Complexification n :=
  1 ⊗ₜ ofMatrix (ℜ M) (selfAdjoint.mem_iff.mp (ℜ M).2) (by
      simp [realPart_apply_coe, trace_smul, trace_add, star_eq_conjTranspose,
        trace_conjTranspose, hM]) +
    Complex.I ⊗ₜ ofMatrix (ℑ M) (selfAdjoint.mem_iff.mp (ℑ M).2) (by
      simp [imaginaryPart_apply_coe, trace_smul, trace_sub, star_eq_conjTranspose,
        trace_conjTranspose, hM])
