import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValueEqAuxFalse
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAuxZeroZero
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeBestEqWin
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeNegEqWinIff
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAuxSingleton
import AFTD.Kb.GameTheoryEconomics.CatchUpValue
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpValueEqWinIff

/-!
# catch_up_value_pair

Topic: combinatorial_games   Node: 1832359c8db9

For any natural numbers x < y, the game value of Catch-Up played on the two-element set {x, y} is CatchUpOutcome.win.
-/

/-- In Catch-Up played on two distinct pieces {x, y} with x < y, the first player wins by choosing the larger piece y. -/
theorem catch_up_value_pair (x y : ℕ) (hxy : x < y) :
    catch_up_value {x, y} = CatchUpOutcome.win := by
  have hne : ({x, y} : Finset ℕ).Nonempty := by simp
  rw [catch_up_value_eq_win_iff _ hne]
  refine ⟨y, by simp, ?_⟩
  rw [Finset.erase_insert_of_ne (ne_of_lt hxy), Finset.erase_singleton, Finset.insert_empty]
  rw [catch_up_value_aux_singleton]
  split_ifs with h1 h2
  · omega
  · rfl
  · omega
