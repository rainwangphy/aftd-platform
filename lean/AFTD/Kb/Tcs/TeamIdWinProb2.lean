import AFTD.Prelude
import AFTD.Kb.Tcs.TeamWinProb
import AFTD.Kb.Tcs.TeamHalfOdd
import AFTD.Kb.Tcs.TeamP2

/-!
# team_id_winProb2

Topic: algorithms   Node: 187247f821c4

In the strengthened instance the identity line-up (all edges 1/2) wins with probability exactly 1/2.
-/

lemma team_id_winProb2 (m : ℕ) : team_winProb (team_P2 m) 1 = 1 / 2 := by
  unfold team_winProb
  have hP : (fun i : Fin (2 * m + 3) => team_P2 m i ((1 : Equiv.Perm (Fin (2 * m + 3))) i))
      = fun _ => (1 / 2 : ℝ) := by
    funext i; simp [team_P2]
  rw [hP, List.ofFn_const, show (2 * m + 3) / 2 + 1 = m + 2 by omega]
  exact team_half_odd m
