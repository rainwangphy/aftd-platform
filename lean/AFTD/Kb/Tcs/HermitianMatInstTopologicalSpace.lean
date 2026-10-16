import AFTD.Prelude
import AFTD.Kb.Tcs.HermitianMat
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
import AFTD.Kb.Tcs.HermitianMatInstCoeMatrix
import AFTD.Kb.Tcs.HermitianMatInstFun
import AFTD.Kb.Tcs.HermitianMatInstAddGroup
import AFTD.Kb.Tcs.HermitianMatInstUniqueOfIsEmpty
import AFTD.Kb.Tcs.HermitianMatInstSMul

/-!
# HermitianMat.instTopologicalSpace

Topic: quantum   Node: e0920eb36874

Provenance: formalization of a published result. Source: QuantumInfo, `HermitianMat.instTopologicalSpace`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HermitianMat/Basic.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

HermitianMat.instTopologicalSpace
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α R 𝕜 : Type*} {m n : Type*} in
variable [Star R] [TrivialStar R] in
variable [RCLike 𝕜] in
variable [AddGroup α] [StarAddMonoid α] in
variable [TopologicalSpace α] in
instance HermitianMat.instTopologicalSpace : TopologicalSpace (HermitianMat n α) :=
  inferInstanceAs (TopologicalSpace (selfAdjoint _))

/- Amusingly, if we don't tag this fun_prop, then fun_prop fails to prove other things! Because
it will look through and see that `HermitianMat.mat` is `Subtype.val` *here*, but not in downstream
applications of the tactic. -/
