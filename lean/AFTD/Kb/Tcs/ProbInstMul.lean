import AFTD.Prelude
import AFTD.Kb.Tcs.Prob
import AFTD.Kb.Tcs.ProbInstCoeReal
import AFTD.Kb.Tcs.ProbCanLift
import AFTD.Kb.Tcs.ProbInstZero
import AFTD.Kb.Tcs.ProbInstOne

/-!
# Prob.instMul

Topic: information   Node: 397b5fc69a07

Provenance: formalization of a published result. Source: QuantumInfo, `Prob.instMul`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ClassicalInfo/Prob.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Prob.instMul
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
noncomputable instance Prob.instMul : Mul Prob :=
  ⟨fun x y ↦ ⟨x.1 * y.1,
    ⟨mul_nonneg x.2.1 y.2.1,
      (mul_le_of_le_one_left y.2.1 x.2.2).trans y.2.2⟩⟩⟩
