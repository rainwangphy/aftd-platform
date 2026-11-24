import AFTD.Prelude
import AFTD.Kb.Tcs.Op2130DecisionGates
import AFTD.Kb.Tcs.Op2130HeightStep

/-!
# op2130_height_double_local

Topic: online_algorithms   Node: d2ff98e0edb4

Provenance: helper lemma. OP-2130, spatial localization of the two-update gate

Two consecutive updates at one path height affect only that site, and their center value is the corresponding two-step scalar gate.
-/

set_option maxHeartbeats 1000000

def op2130_height_double (h : ℕ → ℤ) (j : ℕ) (c1 c2 : Bool) : ℕ → ℤ :=
  op2130_height_step (op2130_height_step h j c1) j c2

theorem op2130_height_double_center (h : ℕ → ℤ) (j : ℕ) (hj : 1 ≤ j) (c1 c2 : Bool) :
    op2130_height_double h j c1 c2 j =
      op2130_gate_update (h (j-1))
        (op2130_gate_update (h (j-1)) (h j) (h (j+1)) c1) (h (j+1)) c2 := by
  have hleft : op2130_height_step h j c1 (j-1) = h (j-1) := by
    simp [op2130_height_step, show j-1 ≠ j by omega]
  have hright : op2130_height_step h j c1 (j+1) = h (j+1) := by
    simp [op2130_height_step]
  have hcenter : op2130_height_step h j c1 j =
      op2130_gate_update (h (j-1)) (h j) (h (j+1)) c1 := by
    simp [op2130_height_step, op2130_gate_update]
  unfold op2130_height_double
  have hout : op2130_height_step (op2130_height_step h j c1) j c2 j =
      op2130_gate_update (op2130_height_step h j c1 (j-1))
        (op2130_height_step h j c1 j) (op2130_height_step h j c1 (j+1)) c2 := by
    simp [op2130_height_step, op2130_gate_update]
  rw [hout,hleft,hcenter,hright]

theorem op2130_height_double_other (h : ℕ → ℤ) (j i : ℕ) (c1 c2 : Bool)
    (hne : i ≠ j) : op2130_height_double h j c1 c2 i = h i := by
  simp [op2130_height_double, op2130_height_step, hne]

theorem op2130_height_double_local (h : ℕ → ℤ) (j : ℕ) (hj : 1 ≤ j) (c1 c2 : Bool) :
    (op2130_height_double h j c1 c2 j =
      op2130_gate_update (h (j-1))
        (op2130_gate_update (h (j-1)) (h j) (h (j+1)) c1) (h (j+1)) c2) ∧
    (∀ i, i ≠ j → op2130_height_double h j c1 c2 i = h i) := by
  exact ⟨op2130_height_double_center h j hj c1 c2,
    fun i hi => op2130_height_double_other h j i c1 c2 hi⟩
