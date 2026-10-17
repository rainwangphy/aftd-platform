import AFTD.Prelude
import AFTD.Kb.Physics.ProbabilisticTheoryOrderedVectorSpace
import AFTD.Kb.Physics.ProbabilisticTheoryOrderUnitSpace
import AFTD.Kb.Physics.ProbabilisticTheoryInstArchimedeanOrderUnitSpaceReal
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpace

/-!
# Real.negMulLog_strictMonoOn

Topic: information   Node: cc4d30fe4c1e

Provenance: formalization of a published result. Source: QuantumInfo, `Real.negMulLog_strictMonoOn`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ClassicalInfo/ForMathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Real.negMulLog_strictMonoOn
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Real in
open NNReal in
theorem Real.negMulLog_strictMonoOn : StrictMonoOn Real.negMulLog (Set.Icc 0 (exp (-1))) := by
  apply strictMonoOn_of_deriv_pos
  · exact convex_Icc 0 (exp (-1))
  · exact continuous_negMulLog.continuousOn
  · intro x hx
    rw [interior_Icc, Set.mem_Ioo] at hx
    linarith only [log_exp (-1), log_lt_log hx.left hx.right, deriv_negMulLog hx.left.ne']
