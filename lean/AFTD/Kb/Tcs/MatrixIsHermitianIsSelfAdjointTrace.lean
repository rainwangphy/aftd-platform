import AFTD.Prelude
import AFTD.Kb.Tcs.IsMaximalSelfAdjoint
import AFTD.Kb.Tcs.IsMaximalSelfAdjointTrivialSelfadjMap
import AFTD.Kb.Tcs.IsMaximalSelfAdjointRCLikeSelfadjMap
import AFTD.Kb.Tcs.InstTrivialStarIsMaximalSelfAdjoint
import AFTD.Kb.Tcs.InstRCLikeIsMaximalSelfAdjoint

/-!
# Matrix.IsHermitian.isSelfAdjoint_trace

Topic: quantum   Node: 21e2024f0f81

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.IsHermitian.isSelfAdjoint_trace`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HermitianMat/Trace.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.IsHermitian.isSelfAdjoint_trace
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {R n m α : Type*} [Star R] [TrivialStar R] [Fintype n] [Fintype m] in
variable [CommRing R] [CommRing α] [StarRing α] [Algebra R α] [IsMaximalSelfAdjoint R α] in
theorem Matrix.IsHermitian.isSelfAdjoint_trace {A : Matrix n n α} (hA : A.IsHermitian) :
    IsSelfAdjoint A.trace := by
  simp [Matrix.trace, IsSelfAdjoint, ← Matrix.star_apply, show star A = A from hA]
