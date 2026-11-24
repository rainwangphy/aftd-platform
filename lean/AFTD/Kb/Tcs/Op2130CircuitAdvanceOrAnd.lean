import AFTD.Prelude
import AFTD.Kb.Tcs.Op2130HeightDoubleLocal
import AFTD.Kb.Tcs.Op2130DecisionGates

/-!
# op2130_circuit_advance_or_and

Topic: online_algorithms   Node: 502182087afa

Provenance: helper lemma. OP-2130, deterministic decision-circuit advance

Four local height updates convert an OR signal to its even encoding and combine it with the next bit in an AND gate.
-/

theorem op2130_circuit_advance_or_and (h : ℕ → ℤ) (p : ℕ) (a x y c1 c2 c3 c4 : Bool)
    (ha : h p = if a then 1 else -1)
    (hx : h (p+1) = if x then 2 else 0)
    (hg : h (p+2) = 2)
    (hy : h (p+3) = if y then 1 else -1) :
    let h1 := op2130_height_double h (p+1) c1 c2
    let h2 := op2130_height_double h1 (p+2) c3 c4
    h2 (p+2) = if a && y then 2 else 0 := by
  let h1 := op2130_height_double h (p+1) c1 c2
  have hc : h1 (p+1) = if a then 2 else 0 := by
    have hcopy := op2130_decision_copy_even (h (p+1)) (h p) c1 c2
      (by rw [hx]; cases x <;> simp) (by rw [ha]; cases a <;> simp)
    have hc0 := op2130_height_double_center h (p+1) (by omega) c1 c2
    have hn : p+1-1=p := by omega
    rw [hn] at hc0
    have hg2 : p+1+1=p+2 := by omega
    rw [hg2, hg] at hc0
    change h1 (p+1) = _ at hc0
    apply hc0.trans
    cases a <;> simpa [ha] using hcopy
  have hg1 : h1 (p+2) = 2 := by
    dsimp only [h1]
    rw [op2130_height_double_other h (p+1) (p+2) c1 c2 (by omega), hg]
  have hy1 : h1 (p+3) = if y then 1 else -1 := by
    dsimp only [h1]
    rw [op2130_height_double_other h (p+1) (p+3) c1 c2 (by omega), hy]
  have hand := op2130_decision_and (h1 (p+1)) (h1 (p+3)) c3 c4
    (by rw [hc]; cases a <;> simp) (by rw [hy1]; cases y <;> simp)
  change op2130_height_double h1 (p+2) c3 c4 (p+2) = _
  rw [op2130_height_double_center h1 (p+2) (by omega) c3 c4]
  simp only [show p+2-1=p+1 by omega, hg1, hc, hy1] at *
  cases a <;> cases y <;> simpa using hand
