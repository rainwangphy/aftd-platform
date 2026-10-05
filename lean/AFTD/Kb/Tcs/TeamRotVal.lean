import AFTD.Prelude

/-!
# team_rot_val

Topic: algorithms   Node: 91daad91eae9

The rotation i ↦ i + 1 (mod n) in coordinates.
-/

/-- The rotation `i ↦ i + 1 (mod n)` in coordinates. -/
lemma team_rot_val (m : ℕ) (i : Fin (2 * m + 3)) :
    (finRotate (2 * m + 3) i).val = if i.val = 2 * m + 2 then 0 else i.val + 1 := by
  have hc := coe_finRotate (n := 2 * m + 2) i
  by_cases hl : i = Fin.last (2 * m + 2)
  · rw [if_pos hl] at hc
    rw [hc]
    subst hl
    simp
  · rw [if_neg hl] at hc
    rw [hc]
    have : i.val ≠ 2 * m + 2 := fun h => hl (Fin.ext (by simp [h]))
    simp [this]
