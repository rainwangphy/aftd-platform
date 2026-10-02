import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAux
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeBest

/-!
# catch_up_value_aux_singleton

Topic: combinatorial_games   Node: 62f5ff036995

In a Catch-Up position with a single remaining piece x, current score s_me, and opponent score s_opp, the game value for the mover is win if s_me + x > s_opp, loss if s_me + x < s_opp, and draw if s_me + x = s_opp, independently of the isFirstMove flag.
-/

lemma catch_up_value_aux_singleton_best (o : CatchUpOutcome) :
    CatchUpOutcome.best [o] = o := by
  cases o <;> rfl

lemma catch_up_value_aux_singleton_attach_toList (x : ℕ) :
    ({x} : Finset ℕ).attach.toList = [⟨x, Finset.mem_singleton_self x⟩] := by
  have h : ({x} : Finset ℕ).attach = {⟨x, Finset.mem_singleton_self x⟩} := by
    ext ⟨y, hy⟩
    simp [Finset.mem_singleton.mp hy]
  rw [h]
  simp

lemma catch_up_value_aux_singleton_empty_eval (s1 s2 : ℕ) (b : Bool) :
    catch_up_value_aux ∅ s1 s2 b =
      if s1 > s2 then CatchUpOutcome.win
      else if s2 > s1 then CatchUpOutcome.loss
      else CatchUpOutcome.draw := by
  rw [catch_up_value_aux.eq_def]
  simp

/-- Endgame valuation of Catch-Up with one remaining piece. -/
theorem catch_up_value_aux_singleton (x : ℕ) (s_me s_opp : ℕ) (isFirstMove : Bool) :
    catch_up_value_aux {x} s_me s_opp isFirstMove =
      if s_me + x > s_opp then CatchUpOutcome.win
      else if s_me + x < s_opp then CatchUpOutcome.loss
      else CatchUpOutcome.draw := by
  rw [catch_up_value_aux.eq_def]
  simp only [Finset.singleton_ne_empty, ↓reduceIte, Finset.sum_singleton]
  rw [catch_up_value_aux_singleton_attach_toList]
  simp only [List.map_cons, List.map_nil, catch_up_value_aux_singleton_best, Finset.erase_singleton]
  rw [catch_up_value_aux_singleton_empty_eval, catch_up_value_aux_singleton_empty_eval]
  split_ifs <;> first | rfl | omega
