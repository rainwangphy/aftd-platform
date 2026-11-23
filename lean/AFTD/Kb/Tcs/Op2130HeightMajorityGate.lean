import AFTD.Prelude
import AFTD.Kb.Tcs.Op2130HeightStep
import AFTD.Kb.Tcs.Op2130HeightClear
import AFTD.Kb.Tcs.Op2130HeightGate
import AFTD.Kb.Tcs.Op2130HeightClearMirror

/-!
# op2130_height_majority_gate

Topic: online_algorithms   Node: 220beb3d52de

Provenance: helper lemma. OP-2130, forced signal circuit on path heights

Two isolated signed unit heights separated by one zero can be combined into a single isolated majority signal in three updates.
-/

theorem op2130_height_majority_gate (h : ℕ → ℤ) (p : ℕ) (hp : 2 ≤ p)
    (x y : ℤ) (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1)
    (hLL : h (p-2) = 0) (hL : h (p-1) = x) (hC : h p = 0)
    (hR : h (p+1) = y) (hRR : h (p+2) = 0) (c cl cr : Bool) :
    let z : ℤ := if x = y then x else if c then 1 else -1
    op2130_height_step (op2130_height_step (op2130_height_step h p c) (p-1) cl) (p+1) cr =
      Function.update (Function.update (Function.update h p z) (p-1) 0) (p+1) 0 := by
  dsimp only
  let z : ℤ := if x = y then x else if c then 1 else -1
  have hz : z = 1 ∨ z = -1 := by
    dsimp [z]
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> cases c <;> simp
  have hgate : op2130_height_step h p c = Function.update h p z :=
    op2130_height_gate h p x y hx hy hL hC hR c
  rw [hgate]
  have hleft : op2130_height_step (Function.update h p z) (p-1) cl =
      Function.update (Function.update h p z) (p-1) 0 := by
    apply op2130_height_clear _ _ x z hx hz
    · have h1 : p-1-1 = p-2 := by omega
      have h2 : p-2 ≠ p := by omega
      simp [h1, h2, hLL]
    · have h1 : p-1 ≠ p := by omega
      simp [h1, hL]
    · have h1 : p-1+1 = p := by omega
      simp [h1]
  rw [hleft]
  apply op2130_height_clear_mirror _ _ y z hy hz
  · have h1 : p+1-1 = p := by omega
    have h2 : p ≠ p-1 := by omega
    simp [h1, h2]
  · have h1 : p+1 ≠ p := by omega
    have h2 : p+1 ≠ p-1 := by omega
    simp [h1, h2, hR]
  · have h1 : p+1+1 = p+2 := by omega
    have h2 : p+2 ≠ p := by omega
    have h3 : p+2 ≠ p-1 := by omega
    simp [h1, h2, h3, hRR]
