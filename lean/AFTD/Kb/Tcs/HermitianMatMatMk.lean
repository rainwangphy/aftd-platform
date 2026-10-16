import AFTD.Prelude
import AFTD.Kb.Tcs.HermitianMatMat
import AFTD.Kb.Tcs.HermitianMat
import AFTD.Kb.Tcs.HermitianMatValEqCoe
import AFTD.Kb.Tcs.HermitianMatInstCoeMatrix

/-!
# HermitianMat.mat_mk

Topic: quantum   Node: a84b2d97350e

Provenance: formalization of a published result. Source: QuantumInfo, `HermitianMat.mat_mk`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HermitianMat/Basic.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

HermitianMat.mat_mk
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open HermitianMat in
variable {α R 𝕜 : Type*} {m n : Type*} in
variable [Star R] [TrivialStar R] in
variable [RCLike 𝕜] in
variable [AddGroup α] [StarAddMonoid α] in
@[simp]
theorem HermitianMat.mat_mk (x : Matrix n n α) (h) : mat ⟨x, h⟩ = x := by
  rfl
