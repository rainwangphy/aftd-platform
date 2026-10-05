import AFTD.Prelude
import AFTD.Kb.Tcs.TeamT2

/-!
# team_T2_mem

Topic: algorithms   Node: 2f234cb7e109

If b is in [0,1], every entry of the list 0,b,...,0 is in [0,1].
-/

lemma team_T2_mem (b : ℝ) (hb : 0 ≤ b ∧ b ≤ 1) (m : ℕ) : ∀ x ∈ team_T2 b m, 0 ≤ x ∧ x ≤ 1 := by
  induction m with
  | zero => intro x hx; simp [team_T2] at hx; subst hx; norm_num
  | succ m ih =>
    intro x hx
    simp only [team_T2, List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · norm_num
    · exact hb
    · exact ih x hx
