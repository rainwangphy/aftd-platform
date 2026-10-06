import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAux
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeBestEqDraw
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeNegEqDrawIff
import AFTD.Kb.GameTheoryEconomics.CatchUpSumInvariant
import AFTD.Kb.GameTheoryEconomics.CatchUpScoreDiffOddOfOddSum
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome

/-!
# catch_up_value_aux_ne_draw_of_odd_sum

Topic: combinatorial_games   Node: 0c02e681390e

Provenance: formalization of a published result. Source: Catch-Up: A Game in Which the Lead Alternates (Game & Puzzle Design 1(2), 2015), Sec. 2.6 and Appendix 5.1 (an odd total cannot be split evenly, so no draw); stated for arbitrary positions (scores plus remaining sum odd)

In Catch-Up, if the sum of remaining piece values and player scores is odd, the mover cannot achieve a draw.
-/

/-- In any Catch-Up position, if the total sum of remaining pieces and both player scores is odd, the game value cannot be a draw. -/
theorem catch_up_value_aux_ne_draw_of_odd_sum (remaining : Finset ℕ) (s_me s_opp : ℕ) (isFirstMove : Bool)
    (h_odd : Odd (remaining.sum (fun x => x) + s_me + s_opp)) :
    catch_up_value_aux remaining s_me s_opp isFirstMove ≠ CatchUpOutcome.draw := by
  rw [catch_up_value_aux.eq_def]
  by_cases hr : remaining = ∅
  · subst hr
    simp only [Finset.sum_empty, zero_add] at h_odd
    rcases h_odd with ⟨k, hk⟩
    simp only [ite_true]
    split_ifs
    · intro h; cases h
    · intro h; cases h
    · intro _
      omega
  · simp only [hr, ite_false]
    by_cases h_lt : s_me + ∑ x ∈ remaining, x < s_opp
    · simp only [h_lt, ite_true]
      intro h; cases h
    · simp only [h_lt, ite_false]
      intro h_draw
      rw [catch_up_outcome_best_eq_draw] at h_draw
      obtain ⟨-, h_in⟩ := h_draw
      rw [List.mem_map] at h_in
      obtain ⟨⟨x, hx⟩, -, h_eq⟩ := h_in
      dsimp at h_eq
      have h_sum_inv := catch_up_sum_invariant remaining x s_me s_opp hx
      split_ifs at h_eq
      · rw [catch_up_outcome_neg_eq_draw_iff] at h_eq
        have h_odd' : Odd ((remaining.erase x).sum (fun y => y) + s_opp + (s_me + x)) := by
          have : (remaining.erase x).sum (fun y => y) + s_opp + (s_me + x) =
                 (remaining.erase x).sum (fun y => y) + (s_me + x) + s_opp := by omega
          rw [this, h_sum_inv]
          exact h_odd
        exact catch_up_value_aux_ne_draw_of_odd_sum (remaining.erase x) s_opp (s_me + x) false h_odd' h_eq
      · rw [catch_up_outcome_neg_eq_draw_iff] at h_eq
        have h_odd' : Odd ((remaining.erase x).sum (fun y => y) + s_opp + (s_me + x)) := by
          have : (remaining.erase x).sum (fun y => y) + s_opp + (s_me + x) =
                 (remaining.erase x).sum (fun y => y) + (s_me + x) + s_opp := by omega
          rw [this, h_sum_inv]
          exact h_odd
        exact catch_up_value_aux_ne_draw_of_odd_sum (remaining.erase x) s_opp (s_me + x) false h_odd' h_eq
      · have h_odd' : Odd ((remaining.erase x).sum (fun y => y) + (s_me + x) + s_opp) := by
          rw [h_sum_inv]
          exact h_odd
        exact catch_up_value_aux_ne_draw_of_odd_sum (remaining.erase x) (s_me + x) s_opp false h_odd' h_eq
termination_by remaining.card
decreasing_by
  all_goals exact Finset.card_erase_lt_of_mem hx
