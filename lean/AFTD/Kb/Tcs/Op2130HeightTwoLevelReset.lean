import AFTD.Prelude
import AFTD.Kb.Tcs.Op2130HeightStep
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# op2130_height_two_level_reset

Topic: online_algorithms   Node: 7f1f13dc5e71

Provenance: helper lemma. OP-2130, two-level path-height dynamics

When a site and its two neighbors have heights in {-1,1}, two consecutive greedy height updates replace the site with the common neighbor sign when neighbors agree and with the second fair coin sign when they differ.
-/

def op2130_local_height (l m r : ℤ) (c : Bool) : ℤ :=
  m + if 2*m < l+r then 1 else if l+r < 2*m then -1 else if c then 1 else -1

theorem op2130_local_two_level_reset (l m r : ℤ) (c1 c2 : Bool)
    (hl : l = 1 ∨ l = -1) (hm : m = 1 ∨ m = -1) (hr : r = 1 ∨ r = -1) :
    op2130_local_height l (op2130_local_height l m r c1) r c2 =
      if l = r then l else if c2 then 1 else -1 := by
  rcases hl with rfl | rfl <;> rcases hm with rfl | rfl <;>
    rcases hr with rfl | rfl <;> cases c1 <;> cases c2 <;>
    norm_num [op2130_local_height]

theorem op2130_height_two_level_reset (h : ℕ → ℤ) (j : ℕ) (hj : 1 ≤ j) (c1 c2 : Bool)
    (hl : h (j-1) = 1 ∨ h (j-1) = -1)
    (hm : h j = 1 ∨ h j = -1)
    (hr : h (j+1) = 1 ∨ h (j+1) = -1) :
    op2130_height_step (op2130_height_step h j c1) j c2 j =
      if h (j-1) = h (j+1) then h (j-1) else if c2 then 1 else -1 := by
  have hn1 : j-1 ≠ j := by omega
  have hp1 : j+1 ≠ j := by omega
  have ha : op2130_height_step h j c1 (j-1) = h (j-1) := by
    simp [op2130_height_step, hn1]
  have hb : op2130_height_step h j c1 j =
      op2130_local_height (h (j-1)) (h j) (h (j+1)) c1 := by
    simp [op2130_height_step, op2130_local_height]
  have hc : op2130_height_step h j c1 (j+1) = h (j+1) := by
    simp [op2130_height_step, hp1]
  have hd : op2130_height_step (op2130_height_step h j c1) j c2 j =
      op2130_local_height (op2130_height_step h j c1 (j-1))
        (op2130_height_step h j c1 j) (op2130_height_step h j c1 (j+1)) c2 := by
    simp [op2130_height_step, op2130_local_height]
  rw [hd, ha, hb, hc]
  exact op2130_local_two_level_reset (h (j-1)) (h j) (h (j+1)) c1 c2 hl hm hr
