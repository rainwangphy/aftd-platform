import AFTD.Prelude
import AFTD.Kb.Tcs.HermitianMat
import AFTD.Kb.Tcs.HermitianMatNonSingular
import AFTD.Kb.Tcs.HermitianMatKer
import AFTD.Kb.Tcs.HermitianMatMat
import AFTD.Kb.Tcs.HermitianMatNonSingularIffDetNeZero
import AFTD.Kb.Tcs.HermitianMatMemKerIffMulVecZero
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
import AFTD.Kb.Tcs.HermitianMatKerReindexLeIff
import AFTD.Kb.Tcs.HermitianMatTraceSmul
import AFTD.Kb.Tcs.HermitianMatTraceZero
import AFTD.Kb.Tcs.HermitianMatTraceAdd
import AFTD.Kb.Tcs.HermitianMatTraceNeg
import AFTD.Kb.Tcs.HermitianMatTraceSub
import AFTD.Kb.Tcs.HermitianMatTraceKronecker
import AFTD.Kb.Tcs.HermitianMatTraceEqTraceTrivial
import AFTD.Kb.Tcs.HermitianMatTraceOne
import AFTD.Kb.Tcs.HermitianMatTraceEqTraceRc
import AFTD.Kb.Tcs.HermitianMatTraceReindex
import AFTD.Kb.Tcs.HermitianMatTraceLeftMat
import AFTD.Kb.Tcs.HermitianMatTraceLeftAdd
import AFTD.Kb.Tcs.HermitianMatTraceLeftNeg
import AFTD.Kb.Tcs.HermitianMatTraceLeftSub
import AFTD.Kb.Tcs.HermitianMatTraceRightMat
import AFTD.Kb.Tcs.HermitianMatTraceRightAdd
import AFTD.Kb.Tcs.HermitianMatTraceRightNeg
import AFTD.Kb.Tcs.HermitianMatTraceRightSub
import AFTD.Kb.Tcs.HermitianMatTraceLeftSmul
import AFTD.Kb.Tcs.HermitianMatTraceRightSmul
import AFTD.Kb.Tcs.HermitianMatTraceLeftTrace
import AFTD.Kb.Tcs.HermitianMatTraceRightTrace
import AFTD.Kb.Tcs.HermitianMatTraceLeftKron
import AFTD.Kb.Tcs.HermitianMatTraceRightKron
import AFTD.Kb.Tcs.HermitianMatIsUnitMatOfNonSingular
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
import AFTD.Kb.Tcs.HermitianMatInstPartialOrder
import AFTD.Kb.Tcs.HermitianMatInstIsOrderedAddMonoid
import AFTD.Kb.Tcs.HermitianMatInstZeroLEOneClass
import AFTD.Kb.Tcs.HermitianMatInstIsStrictOrderedModuleReal
import AFTD.Kb.Tcs.HermitianMatInstPosSMulMonoReal
import AFTD.Kb.Tcs.HermitianMatInstSMulPosMonoReal
import AFTD.Kb.Tcs.HermitianMatInstPosSMulReflectLEReal
import AFTD.Kb.Tcs.HermitianMatInstHasInvOfInvertible
import AFTD.Kb.Tcs.HermitianMatInstInvertibleOfHasInv
import AFTD.Kb.Tcs.HermitianMatInstNonSingularOfNat
import AFTD.Kb.Tcs.HermitianMatExt

/-!
# HermitianMat.nonSingular_iff_ker_bot

Topic: quantum   Node: fb3331d56fc7

Provenance: formalization of a published result. Source: QuantumInfo, `HermitianMat.nonSingular_iff_ker_bot`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HermitianMat/NonSingular.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

HermitianMat.nonSingular_iff_ker_bot
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open HermitianMat in
variable {n m R 𝕜 : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] in
variable [CommRing R] [StarRing R] [RCLike 𝕜] in
variable (A : HermitianMat n R) (B : HermitianMat m R) in
variable {A : HermitianMat n 𝕜} {B : HermitianMat m 𝕜} {C : Matrix n n 𝕜} in
open ComplexOrder in
theorem HermitianMat.nonSingular_iff_ker_bot : NonSingular A ↔ A.ker = ⊥ := by
  rw [nonSingular_iff_det_ne_zero];
  have h_det_nonzero_to_ker_trivial : A.mat.det ≠ 0 → A.ker = ⊥ := by
    intro h_det_nonzero
    rw [Submodule.eq_bot_iff]
    have h_inv : Invertible A.mat := by
      convert Matrix.invertibleOfDetInvertible A.mat
      exact invertibleOfNonzero h_det_nonzero
    have h_ker_trivial (x : n → 𝕜) (hx : A.mat.mulVec x = 0) : x = 0 := by
      simpa using congr_arg (h_inv.1.mulVec) hx
    intro x hx
    rw [mem_ker_iff_mulVec_zero] at hx
    exact PiLp.ext (fun i => congr_fun (h_ker_trivial x.ofLp hx) i)
  refine ⟨h_det_nonzero_to_ker_trivial, fun h h' => ?_⟩
  obtain ⟨x, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h'
  have h_inj : Function.Injective (Matrix.mulVecLin A.mat) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hy
    have hm : (WithLp.toLp 2 y) ∈ A.ker := (mem_ker_iff_mulVec_zero A _).mpr hy
    rw [h] at hm
    have := (Submodule.mem_bot (R := 𝕜)).mp hm
    simpa using this
  specialize @h_inj x 0
  simp_all
