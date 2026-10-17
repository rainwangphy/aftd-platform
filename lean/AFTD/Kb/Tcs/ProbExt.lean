import AFTD.Prelude
import AFTD.Kb.Tcs.Prob
import AFTD.Kb.Tcs.ProbCoeZero
import AFTD.Kb.Tcs.ProbCoeOne
import AFTD.Kb.Tcs.ProbCoeMul
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
import AFTD.Kb.Tcs.ProbInstMul
import AFTD.Kb.Tcs.ProbInstCommMonoidWithZero
import AFTD.Kb.Tcs.ProbInstDenselyOrdered
import AFTD.Kb.Tcs.ProbInstCompleteLinearOrder
import AFTD.Kb.Tcs.ProbInstInhabited

/-!
# Prob.ext

Topic: information   Node: 6e7f29188033

Provenance: formalization of a published result. Source: QuantumInfo, `Prob.ext`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ClassicalInfo/Prob.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Prob.ext
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
@[ext] protected theorem Prob.ext {n m : Prob} : (n : ℝ) = (m : ℝ) → n = m :=
  Subtype.ext
