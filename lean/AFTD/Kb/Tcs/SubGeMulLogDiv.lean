import AFTD.Prelude

/-!
# sub_ge_mul_log_div

Topic: quantum   Node: 8e5938e9bc06

Provenance: formalization of a published result. Source: QuantumInfo, `sub_ge_mul_log_div`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Majorization.lean (Copyright (c) 2026 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

sub_ge_mul_log_div
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {d : Type*} [Fintype d] [DecidableEq d] in
lemma sub_ge_mul_log_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    b - a ≥ a * Real.log (b / a) := by
  nlinarith [Real.log_le_sub_one_of_pos (div_pos hb ha), mul_div_cancel₀ b ha.ne']

/- Weak log-majorization of nonneg antitone sequences implies the sum inequality ∑ x_i ≤ ∑ y_i. -/
