import AFTD.Prelude
import AFTD.Kb.Physics.ProbabilisticTheoryOrderedVectorSpace
import AFTD.Kb.Physics.ProbabilisticTheoryOrderUnitSpace
import AFTD.Kb.Physics.ProbabilisticTheoryInstArchimedeanOrderUnitSpaceReal
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpace

/-!
# Real.negMulLog_strictAntiOn

Topic: information   Node: 7811c0b7f0fa

Provenance: formalization of a published result. Source: QuantumInfo, `Real.negMulLog_strictAntiOn`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ClassicalInfo/ForMathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Real.negMulLog_strictAntiOn
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Real in
open NNReal in
theorem Real.negMulLog_strictAntiOn : StrictAntiOn Real.negMulLog (Set.Ici (exp (-1))) := by
  apply strictAntiOn_of_deriv_neg
  · exact convex_Ici (exp (-1))
  · exact continuous_negMulLog.continuousOn
  · intro x hx
    rw [interior_Ici' Set.nonempty_Iio, Set.mem_Ioi] at hx
    have hx' : x ≠ 0 := by grind [exp_nonneg]
    linarith [log_exp (-1), log_lt_log (exp_pos (-1)) hx, deriv_negMulLog hx']
