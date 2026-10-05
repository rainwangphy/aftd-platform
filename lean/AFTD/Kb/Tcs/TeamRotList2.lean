import AFTD.Prelude
import AFTD.Kb.Tcs.TeamTau
import AFTD.Kb.Tcs.TeamP2
import AFTD.Kb.Tcs.TeamT2
import AFTD.Kb.Tcs.TeamT2Length
import AFTD.Kb.Tcs.TeamT2Get
import AFTD.Kb.Tcs.TeamW2
import AFTD.Kb.Tcs.TeamP2Rot

/-!
# team_rot_list2

Topic: algorithms   Node: 41aa321822cc

The edge probabilities of the rotation in the strengthened instance are 3/4 - 3tau/2, 3/4 - 3tau/2, followed by 0, 1-2tau, 0, ..., 0.
-/

lemma team_rot_list2 (m : ℕ) :
    List.ofFn (fun i : Fin (2 * m + 3) => team_P2 m i (finRotate (2 * m + 3) i))
      = (3 / 4 - 3 / 2 * team_tau m) :: (3 / 4 - 3 / 2 * team_tau m)
          :: team_T2 (1 - 2 * team_tau m) m := by
  have hP : (fun i : Fin (2 * m + 3) => team_P2 m i (finRotate (2 * m + 3) i))
      = fun i => team_w2 i := by
    funext i
    exact team_P2_rot m i
  rw [hP]
  apply List.ext_getElem
  · simp [team_T2_length]
  · intro k h1 h2
    rw [List.getElem_ofFn]
    unfold team_w2
    match k, h1, h2 with
    | 0, _, _ => simp
    | 1, _, _ => simp
    | k + 2, h1, h2 =>
      simp only [List.getElem_cons_succ]
      rw [team_T2_get _ m k (by simp [team_T2_length] at h2 ⊢; omega)]
      simp only [show ¬ (k + 2 ≤ 1) by omega, if_false]
      simp
