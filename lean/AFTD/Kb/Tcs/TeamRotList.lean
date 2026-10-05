import AFTD.Prelude
import AFTD.Kb.Tcs.TeamT
import AFTD.Kb.Tcs.TeamTLength
import AFTD.Kb.Tcs.TeamTGet
import AFTD.Kb.Tcs.TeamW
import AFTD.Kb.Tcs.TeamP
import AFTD.Kb.Tcs.TeamRotNext

/-!
# team_rot_list

Topic: algorithms   Node: 02f649ce8292

The rotation line-up has edge probabilities team_w.
-/

/-- The rotation line-up has edge probabilities `team_w`. -/
lemma team_rot_list (m : ℕ) :
    List.ofFn (fun i : Fin (2 * m + 3) => team_P m i (finRotate (2 * m + 3) i))
      = (3 / 4 : ℝ) :: (3 / 4 : ℝ) :: team_T m := by
  have hP : (fun i : Fin (2 * m + 3) => team_P m i (finRotate (2 * m + 3) i))
      = fun i => team_w i := by
    funext i
    obtain ⟨hn, hne⟩ := team_rot_next m i
    simp only [team_P, if_neg hne, if_pos hn]
  rw [hP]
  apply List.ext_getElem
  · simp [team_T_length]
  · intro k h1 h2
    rw [List.getElem_ofFn]
    unfold team_w
    match k, h1, h2 with
    | 0, _, _ => simp
    | 1, _, _ => simp
    | k + 2, h1, h2 =>
      simp only [List.getElem_cons_succ]
      rw [team_T_get m k (by simp [team_T_length] at h2 ⊢; omega)]
      simp only [show ¬ (k + 2 ≤ 1) by omega, if_false]
      simp
