import AFTD.Prelude
import AFTD.Kb.Tcs.TeamTau
import AFTD.Kb.Tcs.TeamV2
import AFTD.Kb.Tcs.TeamV2Bounds
import AFTD.Kb.Tcs.TeamP2

/-!
# team_dual2

Topic: algorithms   Node: f05e9daa5b38

Strict dual slack on every off-diagonal entry.
-/

/-- Strict dual slack on every off-diagonal entry. -/
lemma team_dual2 (m : ℕ) (i j : Fin (2 * m + 3)) (hji : j ≠ i) :
    team_P2 m i j ≤ (1 / 2 - team_v2 i) + team_v2 j - team_tau m := by
  have hi := team_v2_bounds i
  have hj := team_v2_bounds j
  unfold team_P2
  rw [if_neg hji]
  split_ifs
  · linarith
  · linarith
