import AFTD.Prelude
import AFTD.Kb.Tcs.TeamV
import AFTD.Kb.Tcs.TeamRotVal
import AFTD.Kb.Tcs.TeamRotNext
import AFTD.Kb.Tcs.TeamV2
import AFTD.Kb.Tcs.TeamP2
import AFTD.Kb.Tcs.TeamW2

/-!
# team_P2_rot

Topic: algorithms   Node: 691c24e889bf

In the strengthened instance the rotation line-up i -> i+1 uses the cycle edge probabilities team_w2.
-/

lemma team_P2_rot (m : ℕ) (i : Fin (2 * m + 3)) :
    team_P2 m i (finRotate (2 * m + 3) i) = team_w2 i := by
  obtain ⟨hn, hne⟩ := team_rot_next m i
  have hc := team_rot_val m i
  have hi := i.isLt
  simp only [team_P2, if_neg hne, if_pos hn]
  unfold team_v2 team_v team_w2
  generalize finRotate (2 * m + 3) i = j at hc
  split_ifs at hc ⊢ <;> first | ring1 | (exfalso; omega)
