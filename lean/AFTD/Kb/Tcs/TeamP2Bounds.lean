import AFTD.Prelude
import AFTD.Kb.Tcs.TeamTauPos
import AFTD.Kb.Tcs.TeamV2Bounds
import AFTD.Kb.Tcs.TeamP2

/-!
# team_P2_bounds

Topic: algorithms   Node: 87c9978e2fcf

All entries of the strengthened Team Order instance are probabilities in [0,1].
-/

lemma team_P2_bounds (m : ℕ) (i j : Fin (2 * m + 3)) :
    0 ≤ team_P2 m i j ∧ team_P2 m i j ≤ 1 := by
  have hi := team_v2_bounds i
  have hj := team_v2_bounds j
  have ht := team_tau_pos m
  unfold team_P2
  split_ifs <;> constructor <;> linarith
