import AFTD.Prelude
import AFTD.Kb.Tcs.Op2130HeightStep
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# op2130_height_clear

Topic: online_algorithms   Node: 1db424cdf7b4

Provenance: helper lemma. OP-2130, forced signal circuit on path heights

A signed unit height between a zero height and another signed unit height is forced to zero.
-/

theorem op2130_height_clear (h : ℕ → ℤ) (p : ℕ) (x y : ℤ)
    (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1)
    (hL : h (p-1) = 0) (hC : h p = x) (hR : h (p+1) = y) (c : Bool) :
    op2130_height_step h p c = Function.update h p 0 := by
  unfold op2130_height_step
  rw [hL, hC, hR]
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp
