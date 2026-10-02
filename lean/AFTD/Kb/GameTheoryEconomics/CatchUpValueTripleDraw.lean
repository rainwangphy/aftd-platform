import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValue
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAux
import AFTD.Kb.GameTheoryEconomics.CatchUpValueEqDrawIffNotLoss
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAuxSingleton
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAuxEmpty
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeBestEqDraw
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAuxNeLossIff
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAuxNeLossOfNeWin

/-!
# catch_up_value_triple_draw

Topic: combinatorial_games   Node: 90234651ce95

For any natural numbers x < y < z such that x + y = z, the game value of Catch-Up played on the three-element set {x, y, z} is CatchUpOutcome.draw.
-/

/-- For any natural numbers x < y < z such that x + y = z, the game value of Catch-Up played on {x, y, z} is CatchUpOutcome.draw. -/
theorem catch_up_value_triple_draw (x y z : ℕ) (hxy : x < y) (hyz : y < z) (hsum : x + y = z) :
    catch_up_value {x, y, z} = CatchUpOutcome.draw := by
  have hxz : x < z := lt_trans hxy hyz
  have hxy_ne : x ≠ y := ne_of_lt hxy
  have hyz_ne : y ≠ z := ne_of_lt hyz
  have hxz_ne : x ≠ z := ne_of_lt hxz
  have hS : ({x, y, z} : Finset ℕ).Nonempty := ⟨z, by simp⟩

  have herase_x : ({x, y, z} : Finset ℕ).erase x = {y, z} := by
    rw [Finset.erase_insert]
    simp [hxy_ne, hxz_ne]

  have herase_y : ({x, y, z} : Finset ℕ).erase y = {x, z} := by
    rw [Finset.erase_insert_of_ne hxy_ne]
    rw [Finset.erase_insert]
    simp [hyz_ne]

  have herase_z : ({x, y, z} : Finset ℕ).erase z = {x, y} := by
    rw [Finset.erase_insert_of_ne hxz_ne]
    rw [Finset.erase_insert_of_ne hyz_ne]
    rw [Finset.erase_singleton, Finset.insert_empty]

  have h_draw_z : catch_up_value_aux {x, y} 0 z false = CatchUpOutcome.draw := by
    have hne_xy : ({x, y} : Finset ℕ) ≠ ∅ := by simp
    have herase_xy_x : ({x, y} : Finset ℕ).erase x = {y} := Finset.erase_insert (by simp [hxy_ne])
    have herase_xy_y : ({x, y} : Finset ℕ).erase y = {x} := by
      rw [Finset.erase_insert_of_ne hxy_ne, Finset.erase_singleton, Finset.insert_empty]
    rw [catch_up_value_aux.eq_def]
    simp only [hne_xy, if_false]
    have hsum_lt : ¬ (0 + ∑ i ∈ ({x, y} : Finset ℕ), i < z) := by
      simp [hxy_ne]
      omega
    simp only [hsum_lt, if_false]
    rw [catch_up_outcome_best_eq_draw]
    constructor
    · intro h_win
      simp only [List.mem_map, Finset.mem_toList, Finset.mem_attach, true_and] at h_win
      rcases h_win with ⟨⟨w, hw⟩, hw_eq⟩
      have hw_cases : w = x ∨ w = y := by simpa using hw
      cases hw_cases with
      | inl h =>
        subst w
        dsimp only at hw_eq
        simp only [Bool.false_eq_true, ↓reduceIte, ge_iff_le] at hw_eq
        have hlt : ¬ (0 + x ≥ z) := by omega
        simp only [hlt, ↓reduceIte] at hw_eq
        rw [herase_xy_x, catch_up_value_aux_singleton] at hw_eq
        split_ifs at hw_eq; omega
      | inr h =>
        subst w
        dsimp only at hw_eq
        simp only [Bool.false_eq_true, ↓reduceIte, ge_iff_le] at hw_eq
        have hlt : ¬ (0 + y ≥ z) := by omega
        simp only [hlt, ↓reduceIte] at hw_eq
        rw [herase_xy_y, catch_up_value_aux_singleton] at hw_eq
        split_ifs at hw_eq; omega
    · simp only [List.mem_map, Finset.mem_toList, Finset.mem_attach, true_and]
      refine ⟨⟨x, by simp⟩, ?_⟩
      dsimp only
      simp only [Bool.false_eq_true, ↓reduceIte, ge_iff_le]
      have hlt : ¬ (0 + x ≥ z) := by omega
      simp only [hlt, ↓reduceIte]
      rw [herase_xy_x, catch_up_value_aux_singleton]
      split_ifs with h1 h2
      · omega
      · omega
      · rfl

  have h_ne_loss_x : catch_up_value_aux {y, z} 0 x false ≠ CatchUpOutcome.loss := by
    have hrem : ({y, z} : Finset ℕ).Nonempty := ⟨z, by simp⟩
    have hsum_not_lt : ¬ (0 + ∑ i ∈ ({y, z} : Finset ℕ), i < x) := by
      simp [hyz_ne]
      omega
    rw [catch_up_value_aux_ne_loss_iff _ _ _ hrem hsum_not_lt]
    refine ⟨z, by simp, ?_⟩
    have hge : 0 + z ≥ x := by omega
    simp only [hge, ↓reduceIte]
    have herase : ({y, z} : Finset ℕ).erase z = {y} := by
      rw [Finset.erase_insert_of_ne hyz_ne, Finset.erase_singleton, Finset.insert_empty]
    rw [herase, catch_up_value_aux_singleton]
    split_ifs with h1 h2
    · omega
    · omega
    · decide

  have h_ne_loss_y : catch_up_value_aux {x, z} 0 y false ≠ CatchUpOutcome.loss := by
    have hrem : ({x, z} : Finset ℕ).Nonempty := ⟨z, by simp⟩
    have hsum_not_lt : ¬ (0 + ∑ i ∈ ({x, z} : Finset ℕ), i < y) := by
      simp [hxz_ne]
      omega
    rw [catch_up_value_aux_ne_loss_iff _ _ _ hrem hsum_not_lt]
    refine ⟨z, by simp, ?_⟩
    have hge : 0 + z ≥ y := by omega
    simp only [hge, ↓reduceIte]
    have herase : ({x, z} : Finset ℕ).erase z = {x} := by
      rw [Finset.erase_insert_of_ne hxz_ne, Finset.erase_singleton, Finset.insert_empty]
    rw [herase, catch_up_value_aux_singleton]
    split_ifs with h1 h2
    · omega
    · omega
    · decide

  rw [catch_up_value_eq_draw_iff_not_loss _ hS]
  constructor
  · have hz_in : z ∈ ({x, y, z} : Finset ℕ) := by simp
    apply catch_up_value_aux_ne_loss_of_ne_win {x, y, z} hz_in
    rw [herase_z, h_draw_z]
    decide
  · intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · rw [herase_x]
      exact h_ne_loss_x
    · rw [herase_y]
      exact h_ne_loss_y
    · rw [herase_z, h_draw_z]
      decide
