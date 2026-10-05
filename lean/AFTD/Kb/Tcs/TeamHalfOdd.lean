import AFTD.Prelude
import AFTD.Kb.Tcs.TeamTail
import AFTD.Kb.Tcs.TeamHalfSymm

/-!
# team_half_odd

Topic: algorithms   Node: e5244062d2ed

An odd number 2m+3 of fair coins: at least m+2 heads with probability 1/2.
-/

/-- An odd number `2m+3` of fair coins: at least `m+2` heads with probability `1/2`. -/
lemma team_half_odd (m : ℕ) :
    team_tail (List.replicate (2 * m + 3) (1 / 2 : ℝ)) (m + 2) = 1 / 2 := by
  have h := team_half_symm (2 * m + 3) (m + 2) (by omega)
  rw [show 2 * m + 3 + 1 - (m + 2) = m + 2 by omega] at h
  linarith
