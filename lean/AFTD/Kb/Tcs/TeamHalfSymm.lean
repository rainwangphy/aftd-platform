import AFTD.Prelude
import AFTD.Kb.Tcs.TeamTail
import AFTD.Kb.Tcs.TeamTailZero
import AFTD.Kb.Tcs.TeamTailGt

/-!
# team_half_symm

Topic: algorithms   Node: f9251aabdf03

Symmetry of the fair binomial: S_k(t) + S_k(k+1-t) = 1.
-/

/-- Symmetry of the fair binomial: `S_k(t) + S_k(k+1-t) = 1`. -/
lemma team_half_symm (k : ℕ) : ∀ t, t ≤ k + 1 →
    team_tail (List.replicate k (1 / 2 : ℝ)) t
      + team_tail (List.replicate k (1 / 2 : ℝ)) (k + 1 - t) = 1 := by
  induction k with
  | zero =>
    intro t ht
    interval_cases t <;> simp [team_tail]
  | succ k ih =>
    intro t ht
    rcases Nat.eq_zero_or_pos t with h0 | hpos
    · subst h0
      rw [team_tail_zero, team_tail_gt _ _ (by simp)]
      ring
    · rcases Nat.lt_or_ge t (k + 2) with hlt | hge
      · -- 1 ≤ t ≤ k + 1
        rw [List.replicate_succ]
        simp only [team_tail]
        have e1 := ih (t - 1) (by omega)
        have e2 := ih t (by omega)
        have h3 : k + 1 + 1 - t - 1 = k + 1 - t := by omega
        have h4 : k + 1 - (t - 1) = k + 1 + 1 - t := by omega
        rw [h3]
        rw [h4] at e1
        linarith
      · have : t = k + 2 := by omega
        subst this
        rw [team_tail_gt _ _ (by simp), show k + 1 + 1 - (k + 2) = 0 by omega, team_tail_zero]
        ring
