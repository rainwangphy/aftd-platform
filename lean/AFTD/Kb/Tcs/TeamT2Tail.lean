import AFTD.Prelude
import AFTD.Kb.Tcs.TeamTail
import AFTD.Kb.Tcs.TeamT2
import AFTD.Kb.Tcs.TeamTailNonneg
import AFTD.Kb.Tcs.TeamT2Mem

/-!
# team_T2_tail

Topic: algorithms   Node: de23121845e2

For the list 0,b,...,0 with m copies of b, the probability of at least m successes is at least b^m.
-/

lemma team_T2_tail (b : ℝ) (hb : 0 ≤ b ∧ b ≤ 1) (m : ℕ) : b ^ m ≤ team_tail (team_T2 b m) m := by
  induction m with
  | zero => simp [team_T2, team_tail]
  | succ m ih =>
    simp only [team_T2, team_tail]
    rw [show m + 1 - 1 = m by omega]
    have h1 := team_tail_nonneg (team_T2 b m) (team_T2_mem b hb m) (m + 1)
    have h2 := team_tail_nonneg (team_T2 b m) (team_T2_mem b hb m) m
    have hbm : 0 ≤ b ^ m := pow_nonneg hb.1 m
    rw [pow_succ]
    nlinarith
