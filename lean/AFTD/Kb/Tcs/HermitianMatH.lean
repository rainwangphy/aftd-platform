import AFTD.Prelude
import AFTD.Kb.Tcs.HermitianMat
import AFTD.Kb.Tcs.HermitianMatMat
import AFTD.Kb.Tcs.HermitianMatValEqCoe
import AFTD.Kb.Tcs.HermitianMatMatMk
import AFTD.Kb.Tcs.HermitianMatMkMat
import AFTD.Kb.Tcs.HermitianMatInstCoeMatrix

/-!
# HermitianMat.H

Topic: quantum   Node: 4e628f4039a7

Provenance: formalization of a published result. Source: QuantumInfo, `HermitianMat.H`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HermitianMat/Basic.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Alias for HermitianMat.property or HermitianMat.2, this gets the fact that the value is actually `IsHermitian`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open HermitianMat in
variable {α R 𝕜 : Type*} {m n : Type*} in
variable [Star R] [TrivialStar R] in
variable [RCLike 𝕜] in
variable [AddGroup α] [StarAddMonoid α] in
/-- Alias for HermitianMat.property or HermitianMat.2, this gets the fact that the value is actually `IsHermitian`. -/
theorem HermitianMat.H (A : HermitianMat n α) : A.mat.IsHermitian :=
  A.2
