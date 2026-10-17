import AFTD.Prelude
import AFTD.Kb.Tcs.JensenOperatorInequalityHSum
import AFTD.Kb.Tcs.LownerHeinzTheoremL
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockDiagonal
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockDiagonalStar
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProj
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumIncl
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumInclProjSum
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumEquiv
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjHsumInclApply
import AFTD.Kb.Tcs.JensenOperatorInequalityInnerHsumInclHsumIncl
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumInclAdjoint
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjAdjoint
import AFTD.Kb.Tcs.LownerHeinzTheoremInstNontrivialL
import AFTD.Kb.Tcs.LownerHeinzTheoremInstCFCRealSelfAdjoint

/-!
# JensenOperatorInequality.blockDiagonalHom

Topic: quantum   Node: 838cc6838a94

Provenance: formalization of a published result. Source: QuantumInfo, `JensenOperatorInequality.blockDiagonalHom`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/BlockDiagonal.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The `ℝ`-`⋆`-algebra homomorphism sending a pair of operators `(A, B)` to the block-diagonal operator `diag(A, B)` on the Hilbert sum.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open JensenOperatorInequality in
universe u in
open LownerHeinzTheorem in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [Nontrivial ℋ] in
/-- The `ℝ`-`⋆`-algebra homomorphism sending a pair of operators `(A, B)` to the block-diagonal operator `diag(A, B)` on the Hilbert sum. -/
noncomputable def JensenOperatorInequality.blockDiagonalHom : (L ℋ × L ℋ) →⋆ₐ[ℝ] L (HSum ℋ) where
  toFun p := blockDiagonal (ℋ := ℋ) p.1 p.2
  map_one' := by
    ext z
    simp [blockDiagonal]
  map_mul' := by
    intro p q
    ext z i
    fin_cases i <;>
      simp [blockDiagonal, hsumProj, hsumIncl, hsumEquiv, ContinuousLinearMap.mul_def]
  map_zero' := by
    ext z i
    fin_cases i <;> simp [blockDiagonal]
  map_add' := by
    intro p q
    ext z i
    fin_cases i <;>
      simp [blockDiagonal, hsumProj, hsumIncl, hsumEquiv, add_apply]
  commutes' := by
    intro r
    ext z i
    fin_cases i <;> {
      simp [blockDiagonal, hsumProj, hsumIncl, hsumEquiv, Algebra.algebraMap_eq_smul_one]
    }
  map_star' := by
    intro p
    simp
