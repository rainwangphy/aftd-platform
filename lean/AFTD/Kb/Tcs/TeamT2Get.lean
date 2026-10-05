import AFTD.Prelude
import AFTD.Kb.Tcs.TeamT2

/-!
# team_T2_get

Topic: algorithms   Node: a2a284434b16

The k-th entry of the list 0,b,...,0 is 0 at even k and b at odd k.
-/

lemma team_T2_get (b : ℝ) (m : ℕ) (k : ℕ) (hk : k < (team_T2 b m).length) :
    (team_T2 b m)[k] = if k % 2 = 0 then 0 else b := by
  induction m generalizing k with
  | zero =>
    simp [team_T2] at hk
    subst hk; simp [team_T2]
  | succ m ih =>
    match k, hk with
    | 0, _ => simp [team_T2]
    | 1, _ => simp [team_T2]
    | k + 2, hk =>
      simp only [team_T2, List.getElem_cons_succ]
      rw [ih k (by simp [team_T2] at hk; omega)]
      simp
