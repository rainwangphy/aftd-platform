import AFTD.Prelude
import AFTD.Kb.Tcs.Prob
import AFTD.Kb.Tcs.ProbCoeZero
import AFTD.Kb.Tcs.ProbCoeOne
import AFTD.Kb.Tcs.ProbCoeMul
import AFTD.Kb.Tcs.ProbInstCoeReal
import AFTD.Kb.Tcs.ProbCanLift
import AFTD.Kb.Tcs.ProbInstZero
import AFTD.Kb.Tcs.ProbInstOne
import AFTD.Kb.Tcs.ProbInstMul

/-!
# Prob.coe_inf

Topic: information   Node: 1b16da1b432d

Provenance: formalization of a published result. Source: QuantumInfo, `Prob.coe_inf`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ClassicalInfo/Prob.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Prob.coe_inf
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
@[simp, norm_cast]
theorem Prob.coe_inf (x y : Prob) : (x ⊓ y).val = x.val ⊓ y.val :=
  rfl
