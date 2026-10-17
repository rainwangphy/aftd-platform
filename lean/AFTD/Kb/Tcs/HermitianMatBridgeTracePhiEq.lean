import AFTD.Prelude
import AFTD.Kb.Tcs.HermitianMatBridgePhi

/-!
# HermitianMatBridge.trace_Φ_eq

Topic: quantum   Node: 7758a64c6168

Provenance: formalization of a published result. Source: QuantumInfo, `HermitianMatBridge.trace_Φ_eq`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HermitianMat/LiebConcavity.lean (Copyright (c) 2026 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

General trace bridge: the operator trace of Φ(M) equals the matrix trace of M, for any matrix M (not just Hermitian).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open HermitianMatBridge in
variable {d : Type*} [Fintype d] [DecidableEq d] in
/-- General trace bridge: the operator trace of Φ(M) equals the matrix trace of M, for any matrix M (not just Hermitian). -/
lemma HermitianMatBridge.trace_Φ_eq (M : Matrix d d ℂ) :
    (LinearMap.trace ℂ (EuclideanSpace ℂ d)) (Φ M).toLinearMap = M.trace := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun d ℂ).toBasis]
  congr 1
  ext i j
  simp [Φ, Matrix.toEuclideanCLM, EuclideanSpace.basisFun]
