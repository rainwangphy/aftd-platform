import AFTD.Prelude
import AFTD.Kb.Tcs.TeamT

/-!
# team_T_get

Topic: algorithms   Node: ea160ba8a19e

The k-th entry of the alternating list is 0 at even k and 1 at odd k.
-/

lemma team_T_get (m : ℕ) (k : ℕ) (hk : k < (team_T m).length) :
    (team_T m)[k] = if k % 2 = 0 then 0 else 1 := by
  induction m generalizing k with
  | zero =>
    simp [team_T] at hk
    subst hk; simp [team_T]
  | succ m ih =>
    match k, hk with
    | 0, _ => simp [team_T]
    | 1, _ => simp [team_T]
    | k + 2, hk =>
      simp only [team_T, List.getElem_cons_succ]
      rw [ih k (by simp [team_T] at hk; omega)]
      simp
