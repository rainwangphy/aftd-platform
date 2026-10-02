import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpSearch
import AFTD.Kb.GameTheoryEconomics.CatchUpEvalList
import AFTD.Kb.GameTheoryEconomics.CatchUpBestMapEqWinIff
import AFTD.Kb.GameTheoryEconomics.CatchUpBestMapNeLossIff
import AFTD.Kb.GameTheoryEconomics.CatchUpSearchChild

/-!
# catch_up_search_eq

Topic: combinatorial_games   Node: a85e3f937906

For every fuel n, list l, scores and opening flag, the pruned search with flag true returns true exactly when the computable mirror's value is a win, and with flag false exactly when that value is not a loss.
-/

/-- The pruned search decides 'win' and 'not loss' for the computable mirror. -/
theorem catch_up_search_eq (n : ℕ) : ∀ (l : List ℕ) (s_me s_opp : ℕ) (first : Bool),
    (catch_up_search n l s_me s_opp first true = true ↔
        catch_up_eval_list n l s_me s_opp first = .win) ∧
    (catch_up_search n l s_me s_opp first false = true ↔
        catch_up_eval_list n l s_me s_opp first ≠ .loss) := by
  induction n with
  | zero =>
    intro l s_me s_opp first
    simp only [catch_up_search, catch_up_eval_list, if_true, Bool.false_eq_true, if_false,
      decide_eq_true_eq]
    refine ⟨?_, ?_⟩ <;> split_ifs <;> simp <;> omega
  | succ n ih =>
    intro l s_me s_opp first
    cases l with
    | nil =>
      simp only [catch_up_search, catch_up_eval_list, if_true, Bool.false_eq_true, if_false,
        decide_eq_true_eq]
      refine ⟨?_, ?_⟩ <;> split_ifs <;> simp <;> omega
    | cons h t =>
      simp only [catch_up_search, catch_up_eval_list]
      by_cases hlt : s_me + (h :: t).sum < s_opp
      · simp only [hlt, if_true]; simp
      · simp only [hlt, if_false, Bool.not_true, Bool.not_false]
        have hc : ∀ x,
            (if first then (catch_up_eval_list n ((h :: t).erase x) s_opp (s_me + x) false).neg
              else if s_me + x ≥ s_opp then
                (catch_up_eval_list n ((h :: t).erase x) s_opp (s_me + x) false).neg
              else catch_up_eval_list n ((h :: t).erase x) (s_me + x) s_opp false) =
            (if (first || decide (s_opp ≤ s_me + x)) = true then
                (catch_up_eval_list n ((h :: t).erase x) s_opp (s_me + x) false).neg
              else catch_up_eval_list n ((h :: t).erase x) (s_me + x) s_opp false) := by
          intro x
          cases first <;> simp [ge_iff_le]
        simp only [hc, List.any_eq_true, catch_up_best_map_eq_win_iff,
          catch_up_best_map_ne_loss_iff]
        have child := fun x => catch_up_search_child ((first || decide (s_opp ≤ s_me + x)) = true)
          (catch_up_eval_list n ((h :: t).erase x) s_opp (s_me + x) false)
          (catch_up_eval_list n ((h :: t).erase x) (s_me + x) s_opp false)
          _ _ _ _ (ih _ _ _ _) (ih _ _ _ _)
        constructor
        · exact ⟨fun ⟨x, hx, hp⟩ => ⟨x, hx, (child x).1.1 hp⟩,
            fun ⟨x, hx, hp⟩ => ⟨x, hx, (child x).1.2 hp⟩⟩
        · exact ⟨fun ⟨x, hx, hp⟩ => ⟨x, hx, (child x).2.1 hp⟩,
            fun ⟨x, hx, hp⟩ => ⟨x, hx, (child x).2.2 hp⟩⟩
