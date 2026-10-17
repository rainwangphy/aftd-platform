import AFTD.Prelude
import AFTD.Kb.Tcs.Prob
import AFTD.Kb.Tcs.ProbInstMul
import AFTD.Kb.Tcs.ProbCoeMul
import AFTD.Kb.Tcs.ProbCoeZero
import AFTD.Kb.Tcs.ProbCoeOne
import AFTD.Kb.Tcs.ProbCoeInf
import AFTD.Kb.Tcs.ProbCoeSup
import AFTD.Kb.Tcs.ProbZeroLeCoe
import AFTD.Kb.Tcs.ProbCoeLeOne
import AFTD.Kb.Tcs.ProbZeroLe
import AFTD.Kb.Tcs.ProbLeOne
import AFTD.Kb.Tcs.ProbInstCoeReal
import AFTD.Kb.Tcs.ProbCanLift
import AFTD.Kb.Tcs.ProbInstZero
import AFTD.Kb.Tcs.ProbInstOne
import AFTD.Kb.Tcs.ProbInstCommMonoidWithZero
import AFTD.Kb.Tcs.ProbInstDenselyOrdered
import AFTD.Kb.Tcs.ProbInstCompleteLinearOrder
import AFTD.Kb.Tcs.ProbInstInhabited

/-!
# Prob.toReal_mul

Topic: information   Node: bf70a9e26ec4

Provenance: formalization of a published result. Source: QuantumInfo, `Prob.toReal_mul`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ClassicalInfo/Prob.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Prob.toReal_mul
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
@[simp, norm_cast]
theorem Prob.toReal_mul (x y : Prob) : (x * y : Prob) = (x : ℝ) * (y : ℝ) := by
  simp only [coe_mul]
