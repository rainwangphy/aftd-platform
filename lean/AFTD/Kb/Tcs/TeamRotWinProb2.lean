import AFTD.Prelude
import AFTD.Kb.Tcs.TeamTail
import AFTD.Kb.Tcs.TeamWinProb
import AFTD.Kb.Tcs.TeamTau
import AFTD.Kb.Tcs.TeamTauPos
import AFTD.Kb.Tcs.TeamTauLe
import AFTD.Kb.Tcs.TeamTauMulLe
import AFTD.Kb.Tcs.TeamP2
import AFTD.Kb.Tcs.TeamT2
import AFTD.Kb.Tcs.TeamTailNonneg
import AFTD.Kb.Tcs.TeamT2Mem
import AFTD.Kb.Tcs.TeamT2Tail
import AFTD.Kb.Tcs.TeamRotList2

/-!
# team_rot_winProb2

Topic: algorithms   Node: fe17d028e7a3

The rotation line-up of the strengthened instance wins with probability at least 1/2 + 1/40.
-/

/-- The rotation line-up of the strengthened instance wins with probability at least `1/2 + 1/40`. -/
lemma team_rot_winProb2 (m : ℕ) :
    1 / 2 + 1 / 40 ≤ team_winProb (team_P2 m) (finRotate (2 * m + 3)) := by
  unfold team_winProb
  rw [team_rot_list2, show (2 * m + 3) / 2 + 1 = m + 2 by omega]
  set τ := team_tau m with hτ
  have ht0 := team_tau_pos m
  have ht1 := team_tau_le m
  have ht2 := team_tau_mul_le m
  set a : ℝ := 3 / 4 - 3 / 2 * τ with ha
  set b : ℝ := 1 - 2 * τ with hb
  have hb01 : 0 ≤ b ∧ b ≤ 1 := by constructor <;> linarith
  have hmem := team_T2_mem b hb01 m
  have hT := team_T2_tail b hb01 m
  have n1 := team_tail_nonneg _ hmem (m + 1)
  have n0 := team_tail_nonneg _ hmem m
  have n2 := team_tail_nonneg _ hmem (m + 2)
  -- Bernoulli: b^m ≥ 1 - 2τm ≥ 49/50
  have hbern : 1 + (m : ℝ) * (-2 * τ) ≤ (1 + (-2 * τ)) ^ m :=
    one_add_mul_le_pow (by linarith) m
  have hbm : (49 / 50 : ℝ) ≤ b ^ m := by
    rw [hb, show 1 - 2 * τ = 1 + (-2 * τ) by ring]
    nlinarith
  have ha0 : (147 / 200 : ℝ) ≤ a := by rw [ha]; linarith
  have ha1 : a ≤ 1 := by rw [ha]; linarith
  simp only [team_tail]
  rw [show m + 2 - 1 - 1 = m by omega, show m + 2 - 1 = m + 1 by omega]
  have hT' : (49 / 50 : ℝ) ≤ team_tail (team_T2 b m) m := le_trans hbm hT
  have hsq : (147 / 200 : ℝ) * (147 / 200) ≤ a * a := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 ha1) n1, mul_nonneg (sub_nonneg.2 ha1) n2,
    mul_nonneg (sub_nonneg.2 ha1) (mul_nonneg (sub_nonneg.2 ha1) n2),
    mul_nonneg (by linarith : (0 : ℝ) ≤ a) (mul_nonneg (sub_nonneg.2 ha1) n1),
    mul_nonneg (sub_nonneg.2 ha1) (mul_nonneg (by linarith : (0 : ℝ) ≤ a) n1)]
