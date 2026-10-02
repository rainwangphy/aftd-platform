import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValue
import AFTD.Kb.GameTheoryEconomics.CatchUpValueEqWinIff
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAuxLossOfSumLt
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome

/-!
# catch_up_value_triple_win_of_sum_lt

Topic: combinatorial_games   Node: 5e669d151112

For any natural numbers x < y < z such that x + y < z, the game value of Catch-Up played on the three-element set {x, y, z} is CatchUpOutcome.win.
-/

/-- For three pieces with x < y < z and x + y < z, Catch-Up is a first-player win. -/
theorem catch_up_value_triple_win_of_sum_lt (x y z : ℕ) (hxy : x < y) (hyz : y < z) (hsum : x + y < z) :
    catch_up_value {x, y, z} = CatchUpOutcome.win := by
  have hS : ({x, y, z} : Finset ℕ).Nonempty := ⟨z, by simp⟩
  rw [catch_up_value_eq_win_iff _ hS]
  refine ⟨z, by simp, ?_⟩
  have herase : ({x, y, z} : Finset ℕ).erase z = {x, y} := by
    ext a
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hne, h | h | h⟩
      · left; exact h
      · right; exact h
      · subst h; contradiction
    · rintro (rfl | rfl)
      · refine ⟨ne_of_lt (lt_trans hxy hyz), Or.inl rfl⟩
      · refine ⟨ne_of_lt hyz, Or.inr (Or.inl rfl)⟩
  rw [herase]
  have hxy_ne : x ∉ ({y} : Finset ℕ) := by simp [ne_of_lt hxy]
  have hsum' : 0 + ∑ a ∈ ({x, y} : Finset ℕ), a < z := by
    rw [zero_add, Finset.sum_insert hxy_ne, Finset.sum_singleton]
    exact hsum
  exact catch_up_value_aux_loss_of_sum_lt {x, y} 0 z false hsum'
