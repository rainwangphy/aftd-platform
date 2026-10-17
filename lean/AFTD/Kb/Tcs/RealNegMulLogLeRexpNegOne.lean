import AFTD.Prelude
import AFTD.Kb.Tcs.RealNegMulLogStrictMonoOn
import AFTD.Kb.Tcs.RealNegMulLogStrictAntiOn

/-!
# Real.negMulLog_le_rexp_neg_one

Topic: information   Node: fa0c0e86b945

Provenance: formalization of a published result. Source: QuantumInfo, `Real.negMulLog_le_rexp_neg_one`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ClassicalInfo/ForMathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Real.negMulLog_le_rexp_neg_one
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Real in
open NNReal in
theorem Real.negMulLog_le_rexp_neg_one {x : ℝ} (hx : 0 ≤ x) : negMulLog x ≤ exp (-1) := by
  by_cases hp : x < exp (-1)
  · grw [negMulLog_strictMonoOn.monotoneOn (by grind) (by grind) hp.le]
    simp [negMulLog]
  by_cases hp' : Real.exp (-1) < x
  · grw [negMulLog_strictAntiOn.antitoneOn (by grind) (by grind) hp'.le]
    simp [negMulLog]
  · simp [show x = exp (-1) by order, negMulLog]
