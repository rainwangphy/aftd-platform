import AFTD.Prelude
import AFTD.Kb.Tcs.HermitianMat
import AFTD.Kb.Tcs.HermitianMatMat
import AFTD.Kb.Tcs.HermitianMatH
import AFTD.Kb.Tcs.HermitianMatValEqCoe
import AFTD.Kb.Tcs.HermitianMatMatMk
import AFTD.Kb.Tcs.HermitianMatMkMat
import AFTD.Kb.Tcs.HermitianMatMatApply
import AFTD.Kb.Tcs.HermitianMatInstCoeMatrix
import AFTD.Kb.Tcs.HermitianMatInstFun

/-!
# HermitianMat.conjTranspose_mat

Topic: quantum   Node: d2f1e64be185

Provenance: formalization of a published result. Source: QuantumInfo, `HermitianMat.conjTranspose_mat`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HermitianMat/Basic.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

HermitianMat.conjTranspose_mat
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open HermitianMat in
variable {α R 𝕜 : Type*} {m n : Type*} in
variable [Star R] [TrivialStar R] in
variable [RCLike 𝕜] in
variable [AddGroup α] [StarAddMonoid α] in
@[simp]
theorem HermitianMat.conjTranspose_mat (A : HermitianMat n α) :
    A.mat.conjTranspose = A.mat :=
  A.H
