import AFTD.Prelude
import AFTD.Kb.Tcs.Op2130HeightStep
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# op2130_height_wire

Topic: online_algorithms   Node: 71fb1e17442b

Provenance: helper lemma. OP-2130, forced signal circuit on path heights

An isolated sign moves one site to the right in two forced height updates when the adjacent three sites are zero.
-/

theorem op2130_height_wire (h : ℕ → ℤ) (p : ℕ) (hp : 1 ≤ p)
    (s : ℤ) (hs : s = 1 ∨ s = -1)
    (hL : h (p-1) = 0) (hC : h p = s)
    (hR : h (p+1) = 0) (hRR : h (p+2) = 0) (c1 c2 : Bool) :
    op2130_height_step (op2130_height_step h (p+1) c1) p c2 =
      Function.update (Function.update h (p+1) s) p 0 := by
  have hcopy : op2130_height_step h (p+1) c1 = Function.update h (p+1) s := by
    unfold op2130_height_step
    have hh : p + 1 - 1 = p := by omega
    have hh2 : p + 1 + 1 = p + 2 := by omega
    rw [hh, hh2, hC, hR, hRR]
    rcases hs with rfl | rfl <;> simp
  rw [hcopy]
  unfold op2130_height_step
  have hp1 : p ≠ p+1 := by omega
  have hp2 : p-1 ≠ p+1 := by omega
  simp only [Function.update_apply, hp1, hp2, if_false, if_true, hC, hL]
  rcases hs with rfl | rfl <;> simp
