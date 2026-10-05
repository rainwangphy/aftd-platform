import AFTD.Prelude
import AFTD.Kb.Tcs.TeamTail
import AFTD.Kb.Tcs.TeamWins
import AFTD.Kb.Tcs.TeamWinsCons
import AFTD.Kb.Tcs.TeamSumSplit

/-!
# team_tail_eq_sum

Topic: algorithms   Node: 2287a51fcc24

team_tail equals the explicit sum over outcome vectors Σ_ω [t ≤ #wins(ω)] Π_i (q_i if ω_i else 1 - q_i).
-/

open Finset in
/-- `team_tail` equals the explicit sum over outcome vectors `Σ_ω [t ≤ #wins(ω)] Π_i (q_i if ω_i else 1 - q_i)`. -/
theorem team_tail_eq_sum (n : ℕ) (q : Fin n → ℝ) (t : ℕ) :
    team_tail (List.ofFn q) t = ∑ ω : Fin n → Bool,
      (if t ≤ team_wins ω then (1 : ℝ) else 0) * ∏ i, (if ω i = true then q i else 1 - q i) := by
  induction n generalizing t with
  | zero =>
    simp [team_tail, team_wins]
  | succ n ih =>
    rw [List.ofFn_succ]
    simp only [team_tail]
    rw [ih, ih, team_sum_split, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    simp only [team_wins_cons, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, if_true,
      Bool.false_eq_true, if_false, zero_add]
    have : (t - 1 ≤ team_wins ω) ↔ (t ≤ 1 + team_wins ω) := by omega
    by_cases h : t ≤ 1 + team_wins ω
    · rw [if_pos (this.2 h), if_pos h]; ring
    · rw [if_neg (fun h' => h (this.1 h')), if_neg h]; ring
