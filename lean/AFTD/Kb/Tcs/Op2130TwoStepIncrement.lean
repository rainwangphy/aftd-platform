import AFTD.Prelude

/-!
# op2130_two_step_increment

Topic: online_algorithms   Node: 118318fcbae3

Provenance: helper lemma. OP-2130, paired updates at arbitrary integer heights

For any integer neighbor-minus-center imbalance, two consecutive updates at one height have an explicit increment: zero in the central three cases, deterministic ±2 outside them, and a fair-coin choice only at imbalance ±2.
-/

set_option maxHeartbeats 2000000

def op2130_delta_inc (a : ℤ) (c : Bool) : ℤ :=
  if 0 < a then 1 else if a < 0 then -1 else if c then 1 else -1

theorem op2130_two_step_increment (a : ℤ) (c1 c2 : Bool) :
    let d := op2130_delta_inc a c1
    d + op2130_delta_inc (a - 2*d) c2 =
      if 3 ≤ a then 2 else if a = 2 then (if c2 then 2 else 0)
      else if a ≤ -3 then -2 else if a = -2 then (if c2 then 0 else -2) else 0 := by
  cases c1 <;> cases c2 <;> simp only [op2130_delta_inc, Bool.false_eq_true,
    Bool.true_eq_false, if_true, if_false] <;> split_ifs <;> omega
