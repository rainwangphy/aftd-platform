import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValue
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAux
import AFTD.Kb.GameTheoryEconomics.CatchUpValueEqWinIff
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAuxSingleton
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeBestEqLoss

/-!
# catch_up_value_triple_win_of_sum_gt

Topic: combinatorial_games   Node: 9494ed5cc29e

For any natural numbers x < y < z such that x + y > z, the game value of Catch-Up played on the three-element set {x, y, z} is CatchUpOutcome.win.
-/

/-- For any natural numbers x < y < z such that x + y > z, the game value of Catch-Up played on {x, y, z} is CatchUpOutcome.win. -/
theorem catch_up_value_triple_win_of_sum_gt (x y z : ℕ) (hxy : x < y) (hyz : y < z) (hsum : x + y > z) :
    catch_up_value {x, y, z} = CatchUpOutcome.win := by
  have hxz : x < z := lt_trans hxy hyz
  have hyz_ne : y ≠ z := ne_of_lt hyz
  have hne : ({x, y, z} : Finset ℕ).Nonempty := by simp
  rw [catch_up_value_eq_win_iff _ hne]
  refine ⟨x, by simp, ?_⟩
  rw [Finset.erase_insert (by simp [ne_of_lt hxy, ne_of_lt hxz])]
  have hne_yz : ({y, z} : Finset ℕ) ≠ ∅ := by simp
  rw [catch_up_value_aux.eq_def]
  simp only [hne_yz, if_false]
  have hsum_lt : ¬ (0 + ∑ i ∈ ({y, z} : Finset ℕ), i < x) := by
    simp [hyz_ne]
    omega
  simp only [hsum_lt, if_false]
  rw [catch_up_outcome_best_eq_loss]
  intro o ho
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_attach, true_and] at ho
  rcases ho with ⟨⟨w, hw⟩, rfl⟩
  have hw_cases : w = y ∨ w = z := by simpa using hw
  cases hw_cases with
  | inl h =>
    subst w
    dsimp only
    simp only [Bool.false_eq_true, ↓reduceIte, ge_iff_le]
    have hge' : x ≤ 0 + y := by omega
    simp only [hge', ↓reduceIte]
    rw [Finset.erase_insert (by simp [hyz_ne])]
    rw [catch_up_value_aux_singleton]
    split_ifs with h1 h2
    · rfl
    · omega
    · omega
  | inr h =>
    subst w
    dsimp only
    simp only [Bool.false_eq_true, ↓reduceIte, ge_iff_le]
    have hge' : x ≤ 0 + z := by omega
    simp only [hge', ↓reduceIte]
    rw [Finset.erase_insert_of_ne hyz_ne, Finset.erase_singleton, Finset.insert_empty]
    rw [catch_up_value_aux_singleton]
    split_ifs with h1 h2
    · rfl
    · omega
    · omega
