import AFTD.Prelude
import AFTD.Kb.Tcs.Op2130HeightDoubleLocal
import AFTD.Kb.Tcs.Op2130DecisionGates

/-!
# op2130_circuit_advance_and_or

Topic: online_algorithms   Node: 043997e528ad

Provenance: helper lemma. OP-2130, deterministic decision-circuit advance

Four local height updates convert an AND signal to its odd encoding and combine it with the next bit in an OR gate.
-/

theorem op2130_circuit_advance_and_or (h : ℕ → ℤ) (p : ℕ) (a x y c1 c2 c3 c4 : Bool)
    (ha : h p = if a then 2 else 0)
    (hx : h (p+1) = if x then 1 else -1)
    (hax : x = false → a = false)
    (hg : h (p+2) = -1)
    (hy : h (p+3) = if y then 2 else 0) :
    let h1 := op2130_height_double h (p+1) c1 c2
    let h2 := op2130_height_double h1 (p+2) c3 c4
    h2 (p+2) = if a || y then 1 else -1 := by
  let h1 := op2130_height_double h (p+1) c1 c2
  have hc : h1 (p+1) = if a then 1 else -1 := by
    have hcor : h (p+1) = -1 → h p = 0 := by
      rw [hx, ha]
      cases x <;> cases a <;> simp_all
    have hcopy := op2130_decision_copy_odd (h p) (h (p+1)) c1 c2
      (by rw [ha]; cases a <;> simp) (by rw [hx]; cases x <;> simp) hcor
    have hc0 := op2130_height_double_center h (p+1) (by omega) c1 c2
    have hn : p+1-1=p := by omega
    rw [hn] at hc0
    have hg2 : p+1+1=p+2 := by omega
    rw [hg2, hg] at hc0
    change h1 (p+1) = _ at hc0
    apply hc0.trans
    cases a <;> simpa [ha] using hcopy
  have hg1 : h1 (p+2) = -1 := by
    dsimp only [h1]
    rw [op2130_height_double_other h (p+1) (p+2) c1 c2 (by omega), hg]
  have hy1 : h1 (p+3) = if y then 2 else 0 := by
    dsimp only [h1]
    rw [op2130_height_double_other h (p+1) (p+3) c1 c2 (by omega), hy]
  have hor := op2130_decision_or (h1 (p+3)) (h1 (p+1)) c3 c4
    (by rw [hy1]; cases y <;> simp) (by rw [hc]; cases a <;> simp)
  change op2130_height_double h1 (p+2) c3 c4 (p+2) = _
  rw [op2130_height_double_center h1 (p+2) (by omega) c3 c4]
  simp only [show p+2-1=p+1 by omega, hg1, hc, hy1] at *
  cases a <;> cases y <;> simpa using hor
