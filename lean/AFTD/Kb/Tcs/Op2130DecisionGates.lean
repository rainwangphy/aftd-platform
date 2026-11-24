import AFTD.Prelude

/-!
# op2130_decision_gates

Topic: online_algorithms   Node: da1c8d0b2cfe

Provenance: helper lemma. OP-2130, deterministic height decision-list gates

Two local height updates implement AND, OR, and the two required signal conversions on the indicated finite encodings, independently of both coins.
-/

def op2130_gate_update (l m r : ℤ) (coin : Bool) : ℤ :=
  m + if 2*m < l+r then 1 else if l+r < 2*m then -1 else if coin then 1 else -1

theorem op2130_decision_and (x y : ℤ) (c1 c2 : Bool)
    (hx : x = 0 ∨ x = 2) (hy : y = -1 ∨ y = 1) :
    op2130_gate_update x (op2130_gate_update x 2 y c1) y c2 =
      if x = 2 ∧ y = 1 then 2 else 0 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    cases c1 <;> cases c2 <;> norm_num [op2130_gate_update]

theorem op2130_decision_or (x y : ℤ) (c1 c2 : Bool)
    (hx : x = 0 ∨ x = 2) (hy : y = -1 ∨ y = 1) :
    op2130_gate_update y (op2130_gate_update y (-1) x c1) x c2 =
      if x = 2 ∨ y = 1 then 1 else -1 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    cases c1 <;> cases c2 <;> norm_num [op2130_gate_update]

theorem op2130_decision_copy_even (x y : ℤ) (c1 c2 : Bool)
    (hx : x = 0 ∨ x = 2) (hy : y = -1 ∨ y = 1) :
    op2130_gate_update y (op2130_gate_update y x 2 c1) 2 c2 =
      if y = 1 then 2 else 0 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    cases c1 <;> cases c2 <;> norm_num [op2130_gate_update]

theorem op2130_decision_copy_odd (x y : ℤ) (c1 c2 : Bool)
    (hx : x = 0 ∨ x = 2) (hy : y = -1 ∨ y = 1) (hxy : y = -1 → x = 0) :
    op2130_gate_update x (op2130_gate_update x y (-1) c1) (-1) c2 =
      if x = 2 then 1 else -1 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    cases c1 <;> cases c2 <;> norm_num [op2130_gate_update] at *

theorem op2130_decision_gates (x y : ℤ) (c1 c2 : Bool) (hx : x = 0 ∨ x = 2) (hy : y = -1 ∨ y = 1) : (op2130_gate_update x (op2130_gate_update x 2 y c1) y c2 = if x = 2 ∧ y = 1 then 2 else 0) ∧ (op2130_gate_update y (op2130_gate_update y (-1) x c1) x c2 = if x = 2 ∨ y = 1 then 1 else -1) ∧ (op2130_gate_update y (op2130_gate_update y x 2 c1) 2 c2 = if y = 1 then 2 else 0) ∧ ((y = -1 → x = 0) → op2130_gate_update x (op2130_gate_update x y (-1) c1) (-1) c2 = if x = 2 then 1 else -1) := by
  exact ⟨op2130_decision_and x y c1 c2 hx hy, op2130_decision_or x y c1 c2 hx hy, op2130_decision_copy_even x y c1 c2 hx hy, fun h => op2130_decision_copy_odd x y c1 c2 hx hy h⟩
