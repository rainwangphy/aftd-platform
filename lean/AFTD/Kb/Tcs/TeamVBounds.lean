import AFTD.Prelude
import AFTD.Kb.Tcs.TeamV

/-!
# team_v_bounds

Topic: algorithms   Node: d395a1933767

The column potentials of the first dual certificate lie in [0,1/2].
-/

lemma team_v_bounds {m : ℕ} (j : Fin (2 * m + 3)) : 0 ≤ team_v j ∧ team_v j ≤ 1 / 2 := by
  unfold team_v
  split_ifs <;> norm_num
