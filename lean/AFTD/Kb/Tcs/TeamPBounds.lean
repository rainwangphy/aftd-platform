import AFTD.Prelude
import AFTD.Kb.Tcs.TeamW
import AFTD.Kb.Tcs.TeamP

/-!
# team_P_bounds

Topic: algorithms   Node: afbf36ad186d

All entries of the first Team Order instance are probabilities in [0,1].
-/

lemma team_P_bounds (m : ℕ) (i j : Fin (2 * m + 3)) : 0 ≤ team_P m i j ∧ team_P m i j ≤ 1 := by
  unfold team_P team_w
  split_ifs <;> norm_num
