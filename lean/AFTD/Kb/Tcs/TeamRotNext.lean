import AFTD.Prelude
import AFTD.Kb.Tcs.TeamNext
import AFTD.Kb.Tcs.TeamRotVal

/-!
# team_rot_next

Topic: algorithms   Node: 167b33357ca1

The rotation i ↦ i + 1 (mod n) follows the cycle edges.
-/

/-- The rotation `i ↦ i + 1 (mod n)` follows the cycle edges. -/
lemma team_rot_next (m : ℕ) (i : Fin (2 * m + 3)) :
    team_next i (finRotate (2 * m + 3) i) ∧ finRotate (2 * m + 3) i ≠ i := by
  have hc := team_rot_val m i
  have hi := i.isLt
  constructor
  · unfold team_next
    split_ifs at hc with h
    · right; exact ⟨h, hc⟩
    · left; exact hc
  · intro h
    have h' := congrArg Fin.val h
    split_ifs at hc <;> omega
