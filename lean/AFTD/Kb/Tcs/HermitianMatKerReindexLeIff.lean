import AFTD.Prelude
import AFTD.Kb.Tcs.HermitianMat
import AFTD.Kb.Tcs.HermitianMatKer
import AFTD.Kb.Tcs.HermitianMatReindex
import AFTD.Kb.Tcs.LinearEquivEuclideanOfRelabel
import AFTD.Kb.Tcs.HermitianMatKerReindex
import AFTD.Kb.Tcs.HermitianMatValEqCoe
import AFTD.Kb.Tcs.HermitianMatMatMk
import AFTD.Kb.Tcs.HermitianMatMkMat
import AFTD.Kb.Tcs.HermitianMatMatApply
import AFTD.Kb.Tcs.HermitianMatConjTransposeMat
import AFTD.Kb.Tcs.HermitianMatMatZero
import AFTD.Kb.Tcs.HermitianMatMkZero
import AFTD.Kb.Tcs.HermitianMatZeroApply
import AFTD.Kb.Tcs.HermitianMatMatAdd
import AFTD.Kb.Tcs.HermitianMatMatSub
import AFTD.Kb.Tcs.HermitianMatMatNeg
import AFTD.Kb.Tcs.HermitianMatMatSmul
import AFTD.Kb.Tcs.HermitianMatSmulApply
import AFTD.Kb.Tcs.HermitianMatMatFinsetSum
import AFTD.Kb.Tcs.HermitianMatMatOne
import AFTD.Kb.Tcs.HermitianMatMkOne
import AFTD.Kb.Tcs.HermitianMatOneApply
import AFTD.Kb.Tcs.HermitianMatMatInv
import AFTD.Kb.Tcs.HermitianMatZeroInv
import AFTD.Kb.Tcs.HermitianMatOneInv
import AFTD.Kb.Tcs.HermitianMatMatPow
import AFTD.Kb.Tcs.HermitianMatPowZero
import AFTD.Kb.Tcs.HermitianMatZeroPow
import AFTD.Kb.Tcs.HermitianMatOnePow
import AFTD.Kb.Tcs.HermitianMatMatZpow
import AFTD.Kb.Tcs.HermitianMatZpowNatCast
import AFTD.Kb.Tcs.HermitianMatZpowZero
import AFTD.Kb.Tcs.HermitianMatZpowOne
import AFTD.Kb.Tcs.HermitianMatOneZpow
import AFTD.Kb.Tcs.HermitianMatZpowNegOne
import AFTD.Kb.Tcs.HermitianMatInvZpow
import AFTD.Kb.Tcs.HermitianMatImDiagEqZero
import AFTD.Kb.Tcs.HermitianMatComplexImEqZero
import AFTD.Kb.Tcs.HermitianMatConjApplyMat
import AFTD.Kb.Tcs.HermitianMatConjZero
import AFTD.Kb.Tcs.HermitianMatConjOne
import AFTD.Kb.Tcs.HermitianMatConjOneUnitary
import AFTD.Kb.Tcs.HermitianMatConjLinearApply
import AFTD.Kb.Tcs.HermitianMatIsSymmetric
import AFTD.Kb.Tcs.HermitianMatLinZero
import AFTD.Kb.Tcs.HermitianMatLinOne
import AFTD.Kb.Tcs.HermitianMatKerZero
import AFTD.Kb.Tcs.HermitianMatKerOne
import AFTD.Kb.Tcs.HermitianMatSupportZero
import AFTD.Kb.Tcs.HermitianMatSupportOne
import AFTD.Kb.Tcs.HermitianMatKerOrthogonalEqSupport
import AFTD.Kb.Tcs.HermitianMatSupportOrthogonalEqRange
import AFTD.Kb.Tcs.HermitianMatDiagonalMat
import AFTD.Kb.Tcs.HermitianMatDiagonalZero
import AFTD.Kb.Tcs.HermitianMatDiagonalOne
import AFTD.Kb.Tcs.HermitianMatKroneckerMat
import AFTD.Kb.Tcs.HermitianMatZeroKronecker
import AFTD.Kb.Tcs.HermitianMatKroneckerZero
import AFTD.Kb.Tcs.HermitianMatKroneckerOneOne
import AFTD.Kb.Tcs.HermitianMatSpectrumRcLike
import AFTD.Kb.Tcs.LinearEquivOfRelabelRefl
import AFTD.Kb.Tcs.LinearEquivEuclideanOfRelabelRefl
import AFTD.Kb.Tcs.HermitianMatMatReindex
import AFTD.Kb.Tcs.HermitianMatReindexRefl
import AFTD.Kb.Tcs.HermitianMatReindexReindex
import AFTD.Kb.Tcs.HermitianMatReindexZero
import AFTD.Kb.Tcs.HermitianMatReindexOne
import AFTD.Kb.Tcs.HermitianMatReindexAdd
import AFTD.Kb.Tcs.HermitianMatReindexSub
import AFTD.Kb.Tcs.HermitianMatReindexNeg
import AFTD.Kb.Tcs.HermitianMatReindexSmul
import AFTD.Kb.Tcs.HermitianMatReindexConj
import AFTD.Kb.Tcs.HermitianMatInstCoeMatrix
import AFTD.Kb.Tcs.HermitianMatInstFun
import AFTD.Kb.Tcs.HermitianMatInstAddGroup
import AFTD.Kb.Tcs.HermitianMatInstUniqueOfIsEmpty
import AFTD.Kb.Tcs.HermitianMatInstSMul
import AFTD.Kb.Tcs.HermitianMatInstTopologicalSpace
import AFTD.Kb.Tcs.HermitianMatInstContinuousAdd
import AFTD.Kb.Tcs.HermitianMatInstContinuousNeg
import AFTD.Kb.Tcs.HermitianMatInstIsTopologicalAddGroup
import AFTD.Kb.Tcs.HermitianMatInstIsTopologicalAddGroup1
import AFTD.Kb.Tcs.HermitianMatInstContinuousSMulRealComplex
import AFTD.Kb.Tcs.HermitianMatInstT3Space
import AFTD.Kb.Tcs.HermitianMatInstMulAction
import AFTD.Kb.Tcs.HermitianMatInstAddCommGroup
import AFTD.Kb.Tcs.HermitianMatInstModule
import AFTD.Kb.Tcs.HermitianMatInstOne
import AFTD.Kb.Tcs.HermitianMatInstAddCommMonoidWithOne
import AFTD.Kb.Tcs.HermitianMatInstNeZeroOfNatOfNonempty
import AFTD.Kb.Tcs.HermitianMatInstInv
import AFTD.Kb.Tcs.HermitianMatInstPow
import AFTD.Kb.Tcs.HermitianMatInstZPow
import AFTD.Kb.Tcs.HermitianMatFiniteDimensional
import AFTD.Kb.Tcs.HermitianMatInstFaithfulSMulRealOfNonempty
import AFTD.Kb.Tcs.HermitianMatInstAddCommMonoidComplex

/-!
# HermitianMat.ker_reindex_le_iff

Topic: quantum   Node: ea2e580156fe

Provenance: formalization of a published result. Source: QuantumInfo, `HermitianMat.ker_reindex_le_iff`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HermitianMat/Reindex.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

HermitianMat.ker_reindex_le_iff
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open HermitianMat in
variable {d d₂ d₃ d₄ 𝕜 : Type*} [RCLike 𝕜] in
variable (A B : HermitianMat d 𝕜) (e : d ≃ d₂) in
variable [Fintype d] in
variable [Fintype d₂] [DecidableEq d] [DecidableEq d₂] in
@[simp]
theorem HermitianMat.ker_reindex_le_iff :
    (A.reindex e).ker ≤ (B.reindex e).ker ↔ A.ker ≤ B.ker := by
  rw [ker_reindex, ker_reindex]
  apply Submodule.comap_le_comap_iff_of_surjective
  exact LinearEquiv.surjective (LinearEquiv.euclideanOfRelabel 𝕜 e)
