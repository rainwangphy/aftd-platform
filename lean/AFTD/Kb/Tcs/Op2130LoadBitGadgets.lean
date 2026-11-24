import AFTD.Prelude
import AFTD.Kb.Tcs.Op2130DecisionGates
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# op2130_load_bit_gadgets

Topic: online_algorithms   Node: 91512241c711

Provenance: helper lemma. OP-2130, independent-bit loading gadget

The fixed even-bit, odd-bit, and left-reference preparation sequences give the specified Boolean encoding independently of all dummy coins.
-/

theorem op2130_load_even_bit (c d1 d2 d3 d4 d5 : Bool) :
    let step := fun m c => op2130_gate_update 0 m 2 c
    let m := step (step (step (step 5 d1) d2) d3) d4
    m = 1 ∧ step m c = (if c then 2 else 0) ∧
      op2130_gate_update (-3) 0 (if c then 2 else 0) d5 = -1 := by
  cases c <;> cases d1 <;> cases d2 <;> cases d3 <;> cases d4 <;> cases d5 <;>
    norm_num [op2130_gate_update]

theorem op2130_load_odd_bit (c d1 d2 d3 d4 : Bool) :
    let step := fun m c => op2130_gate_update 1 m (-1) c
    let m := step (step (step (-3) d1) d2) d3
    m = 0 ∧ step m c = (if c then 1 else -1) ∧
      op2130_gate_update 5 1 (if c then 1 else -1) d4 = 2 := by
  cases c <;> cases d1 <;> cases d2 <;> cases d3 <;> cases d4 <;>
    norm_num [op2130_gate_update]

theorem op2130_load_left_reference (d1 d2 : Bool) :
    op2130_gate_update 0 (op2130_gate_update 0 (-3) (-1) d1) (-1) d2 = -1 := by
  cases d1 <;> cases d2 <;> norm_num [op2130_gate_update]

theorem op2130_load_bit_gadgets :
  (∀ c d1 d2 d3 d4 d5 : Bool,
    let step := fun m c => op2130_gate_update 0 m 2 c
    let m := step (step (step (step 5 d1) d2) d3) d4
    m = 1 ∧ step m c = (if c then 2 else 0) ∧
      op2130_gate_update (-3) 0 (if c then 2 else 0) d5 = -1) ∧
  (∀ c d1 d2 d3 d4 : Bool,
    let step := fun m c => op2130_gate_update 1 m (-1) c
    let m := step (step (step (-3) d1) d2) d3
    m = 0 ∧ step m c = (if c then 1 else -1) ∧
      op2130_gate_update 5 1 (if c then 1 else -1) d4 = 2) ∧
  (∀ d1 d2 : Bool,
    op2130_gate_update 0 (op2130_gate_update 0 (-3) (-1) d1) (-1) d2 = -1) := by
  exact ⟨op2130_load_even_bit, op2130_load_odd_bit, op2130_load_left_reference⟩
