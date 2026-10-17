import AFTD.Prelude
import AFTD.Kb.Tcs.HermitianMat
import AFTD.Kb.Tcs.HermitianMatMat
import AFTD.Kb.Tcs.HermitianMatInstAddCommGroup
import AFTD.Kb.Tcs.HermitianMatExt
import AFTD.Kb.Tcs.HermitianMatInstAddGroup
import AFTD.Kb.Tcs.HermitianMatMatZero
import AFTD.Kb.Tcs.HermitianMatInstFun
import AFTD.Kb.Tcs.HermitianMatInstOne
import AFTD.Kb.Tcs.HermitianMatMatApply
import AFTD.Kb.Tcs.HermitianMatValEqCoe
import AFTD.Kb.Tcs.HermitianMatMatMk
import AFTD.Kb.Tcs.HermitianMatMkMat
import AFTD.Kb.Tcs.HermitianMatConjTransposeMat
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
import AFTD.Kb.Tcs.HermitianMatInstCoeMatrix
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
import AFTD.Kb.Tcs.HermitianMatInstModule
import AFTD.Kb.Tcs.HermitianMatInstAddCommMonoidWithOne
import AFTD.Kb.Tcs.HermitianMatInstNeZeroOfNatOfNonempty
import AFTD.Kb.Tcs.HermitianMatInstInv
import AFTD.Kb.Tcs.HermitianMatInstPow
import AFTD.Kb.Tcs.HermitianMatInstZPow
import AFTD.Kb.Tcs.HermitianMatFiniteDimensional
import AFTD.Kb.Tcs.HermitianMatInstFaithfulSMulRealOfNonempty
import AFTD.Kb.Tcs.HermitianMatKer

/-!
# HermitianMat.range_le_ker_imp_zero

Topic: quantum   Node: 3ac3d837903b

Provenance: formalization of a published result. Source: QuantumInfo, `HermitianMat.range_le_ker_imp_zero`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HermitianMat/Basic.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

HermitianMat.range_le_ker_imp_zero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open HermitianMat in
variable {α R 𝕜 : Type*} {m n : Type*} in
variable [Star R] [TrivialStar R] in
variable [RCLike 𝕜] in
variable {d d₂ : Type*} [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂] in
theorem HermitianMat.range_le_ker_imp_zero {A : HermitianMat d 𝕜}
    (h : LinearMap.range A.mat.toEuclideanLin ≤ LinearMap.ker A.mat.toEuclideanLin) : A = 0 := by
  rw [HermitianMat.ext_iff, mat_zero]
  ext i j
  have hA_sq : (A.mat * A.mat) = 0 := by
    simp_all only [SetLike.le_def, LinearMap.mem_range, LinearMap.mem_ker, forall_exists_index,
      forall_apply_eq_imp_iff]
    simp_all only [← Matrix.ext_iff, Matrix.mul_apply, mat_apply, Matrix.zero_apply]
    intro i j
    specialize h ( EuclideanSpace.single j 1 )
    simpa [ Matrix.mulVec, dotProduct ] using congr(WithLp.ofLp $(h) i)
  simp_all only [mat_apply, Matrix.zero_apply]
  replace hA_sq := congr_fun ( congr_fun hA_sq i ) i
  simp_all only [Matrix.mul_apply, mat_apply, Matrix.zero_apply] ;
  -- Since $A$ is Hermitian, we have $A i x * A x i = |A i x|^2$.
  have h_abs : ∀ x, (A i x) * (A x i) = ‖A i x‖ ^ 2 := by
    intro x; have := A.2
    simp_all only [val_eq_coe, sq] ;
    have := congr_fun ( congr_fun this i ) x
    simp_all only [Matrix.star_apply, mat_apply, RCLike.star_def] ;
    simp only [← this, mul_comm, RCLike.norm_conj];
    simp [ ← sq, RCLike.mul_conj ];
  simp_rw [h_abs] at hA_sq
  norm_cast at hA_sq
  simp_all [Finset.sum_eq_zero_iff_of_nonneg]
