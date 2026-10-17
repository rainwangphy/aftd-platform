import AFTD.Prelude
import AFTD.Kb.Tcs.Prob
import AFTD.Kb.Tcs.ProbInstCoeReal

/-!
# Prob.canLift

Topic: information   Node: 642738c87638

Provenance: formalization of a published result. Source: QuantumInfo, `Prob.canLift`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ClassicalInfo/Prob.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Prob.canLift
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
noncomputable instance Prob.canLift : CanLift ℝ Prob Subtype.val fun r => 0 ≤ r ∧ r ≤ 1 :=
  Subtype.canLift _
