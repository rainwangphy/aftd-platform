import AFTD.Prelude

/-!
# Prob

Topic: information   Node: 60fde9679071

Provenance: formalization of a published result. Source: QuantumInfo, `Prob`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ClassicalInfo/Prob.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`Prob` is a real number in the interval [0,1]. Similar to NNReal in many definitions, but this allows other nice things more 'safely' such as convex combination.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
open Classical in
/-- `Prob` is a real number in the interval [0,1]. Similar to NNReal in many definitions, but this allows other nice things more 'safely' such as convex combination. -/
@[reducible]
noncomputable def Prob := { p : ℝ // 0 ≤ p ∧ p ≤ 1 }
