import AFTD.Prelude
import AFTD.Kb.Tcs.TeamWins

/-!
# team_wins_cons

Topic: algorithms   Node: e09152cf1e7b

The number of wins of an outcome vector with a prepended result b is [b] plus the number of wins of the rest.
-/

open Finset in
lemma team_wins_cons {n : ℕ} (b : Bool) (ω : Fin n → Bool) :
    team_wins (Fin.cons b ω : Fin (n + 1) → Bool) = (if b = true then 1 else 0) + team_wins ω := by
  unfold team_wins
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
