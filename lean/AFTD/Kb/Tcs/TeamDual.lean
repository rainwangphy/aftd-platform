import AFTD.Prelude
import AFTD.Kb.Tcs.TeamW
import AFTD.Kb.Tcs.TeamNext
import AFTD.Kb.Tcs.TeamP
import AFTD.Kb.Tcs.TeamV
import AFTD.Kb.Tcs.TeamVBounds

/-!
# team_dual

Topic: algorithms   Node: 52c266b0ff80

Dual feasibility: p(i,j) ≤ (1/2 - v_i) + v_j.
-/

/-- Dual feasibility: `p(i,j) ≤ (1/2 - v_i) + v_j`. -/
lemma team_dual (m : ℕ) (i j : Fin (2 * m + 3)) :
    team_P m i j ≤ (1 / 2 - team_v i) + team_v j := by
  have hi := i.isLt
  have hj := j.isLt
  unfold team_P
  by_cases hji : j = i
  · subst hji; simp
  · rw [if_neg hji]
    by_cases hn : team_next i j
    · rw [if_pos hn]
      unfold team_next at hn
      unfold team_w team_v
      rcases hn with h | ⟨h1, h2⟩
      · split_ifs <;> (try norm_num) <;> omega
      · split_ifs <;> (try norm_num) <;> omega
    · rw [if_neg hn]
      have := team_v_bounds i
      have := team_v_bounds j
      linarith
