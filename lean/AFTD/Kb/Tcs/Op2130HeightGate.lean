import AFTD.Prelude
import AFTD.Kb.Tcs.Op2130HeightStep
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# op2130_height_gate

Topic: online_algorithms   Node: 4ad66db16bed

Provenance: helper lemma. OP-2130, forced signal circuit on path heights

Updating a zero height between two independent signed unit heights gives their majority with the supplied tie coin.
-/

theorem op2130_height_gate (h : ℕ → ℤ) (p : ℕ) (x y : ℤ)
    (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1)
    (hL : h (p-1) = x) (hC : h p = 0) (hR : h (p+1) = y) (c : Bool) :
    op2130_height_step h p c =
      Function.update h p (if x = y then x else if c then 1 else -1) := by
  unfold op2130_height_step
  rw [hL, hC, hR]
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> cases c <;> simp
