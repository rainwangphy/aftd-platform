import AFTD.Prelude
import AFTD.Kb.Tcs.TeamTail

/-!
# team_tail_nonneg

Topic: algorithms   Node: d6604e6bd1a9

Upper-tail probabilities of independent events with probabilities in [0,1] are nonnegative.
-/

lemma team_tail_nonneg (L : List ℝ) (hL : ∀ x ∈ L, 0 ≤ x ∧ x ≤ 1) (t : ℕ) :
    0 ≤ team_tail L t := by
  induction L generalizing t with
  | nil => simp [team_tail]; split_ifs <;> norm_num
  | cons p ps ih =>
    have hp := hL p (by simp)
    have ih' : ∀ s, 0 ≤ team_tail ps s := fun s => ih (fun x hx => hL x (by simp [hx])) s
    simp only [team_tail]
    have := ih' (t - 1)
    have := ih' t
    nlinarith
