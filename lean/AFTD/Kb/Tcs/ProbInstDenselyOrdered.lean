import AFTD.Prelude
import AFTD.Kb.Tcs.Prob
import AFTD.Kb.Tcs.ProbCoeZero
import AFTD.Kb.Tcs.ProbCoeOne
import AFTD.Kb.Tcs.ProbCoeMul
import AFTD.Kb.Tcs.ProbCoeInf
import AFTD.Kb.Tcs.ProbCoeSup
import AFTD.Kb.Tcs.ProbInstCoeReal
import AFTD.Kb.Tcs.ProbCanLift
import AFTD.Kb.Tcs.ProbInstZero
import AFTD.Kb.Tcs.ProbInstOne
import AFTD.Kb.Tcs.ProbInstMul
import AFTD.Kb.Tcs.ProbInstCommMonoidWithZero

/-!
# Prob.instDenselyOrdered

Topic: information   Node: e0185523ac08

Provenance: formalization of a published result. Source: QuantumInfo, `Prob.instDenselyOrdered`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ClassicalInfo/Prob.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Prob.instDenselyOrdered
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
noncomputable instance Prob.instDenselyOrdered : DenselyOrdered Prob :=
  show DenselyOrdered (Set.Icc 0 1) from Set.instDenselyOrdered
