import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAux
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeBest
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeNeg

/-!
# catch_up_eval_list

Topic: combinatorial_games   Node: 77031ee5d65f

A computable mirror of catch_up_value_aux: the same Catch-Up recursion on a list of the remaining numbers, by structural recursion on a fuel bound n, so that the kernel can evaluate it.
-/

/-- Computable mirror of `catch_up_value_aux` on a list of the remaining numbers, with fuel `n`. -/
def catch_up_eval_list : ℕ → List ℕ → ℕ → ℕ → Bool → CatchUpOutcome := fun
  | 0, _, s_me, s_opp, _ =>
      if s_me > s_opp then .win else if s_opp > s_me then .loss else .draw
  | n + 1, l, s_me, s_opp, first =>
      match l with
      | [] => if s_me > s_opp then .win else if s_opp > s_me then .loss else .draw
      | _ :: _ =>
        if s_me + l.sum < s_opp then .loss
        else CatchUpOutcome.best (l.map fun x =>
          if first then (catch_up_eval_list n (l.erase x) s_opp (s_me + x) false).neg
          else if s_me + x ≥ s_opp then
            (catch_up_eval_list n (l.erase x) s_opp (s_me + x) false).neg
          else catch_up_eval_list n (l.erase x) (s_me + x) s_opp false)
