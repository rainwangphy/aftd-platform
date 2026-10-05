import AFTD.Prelude
import AFTD.Kb.Tcs.TeamWinProb
import AFTD.Kb.Tcs.TeamIsMaxWeight
import AFTD.Kb.Tcs.TeamIsOptimal
import AFTD.Kb.Tcs.TeamP2
import AFTD.Kb.Tcs.Team2UniqueMaxWeight
import AFTD.Kb.Tcs.TeamIdWinProb2
import AFTD.Kb.Tcs.TeamRotWinProb2

/-!
# team_gap_unique

Topic: algorithms   Node: 8ec6a3d572c8

Quantitative form of the strengthened counterexample: for every m, the identity is the unique maximum-weight matching, its edges are all 1/2, and every optimal line-up beats it by at least 1/40.
-/

/-- Quantitative form of the strengthened counterexample: for every `m`, the identity is the unique maximum-weight matching, its edges are all `1/2`, and every optimal line-up beats it by at least `1/40`. -/
theorem team_gap_unique (m : ℕ) (O : Equiv.Perm (Fin (2 * m + 3)))
    (hO : team_isOptimal (team_P2 m) O) :
    (∀ M, team_isMaxWeight (team_P2 m) M ↔ M = 1) ∧
      (∀ i, team_P2 m i ((1 : Equiv.Perm (Fin (2 * m + 3))) i) = 1 / 2) ∧
      team_winProb (team_P2 m) 1 + 1 / 40 ≤ team_winProb (team_P2 m) O := by
  refine ⟨team2_unique_maxWeight m, fun i => by simp [team_P2], ?_⟩
  have := hO (finRotate (2 * m + 3))
  have := team_rot_winProb2 m
  rw [team_id_winProb2]
  linarith
