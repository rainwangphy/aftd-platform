import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SwingTableEqZeroOfLt
import AFTD.Kb.GameTheoryEconomics.IsSimpleGame
import AFTD.Kb.GameTheoryEconomics.SwingTable

/-!
# exists_simple_games_ne_of_swing_table_eq

Topic: general_equilibrium   Node: 9709c043e338

Fried's Example 10.1: the five-player simple games with minimal winning coalitions {1,2,3}, {0,2,4}, {0,3,4}, {1,3,4} and {0,1,2}, {0,3,4}, {1,3,4}, {2,3,4} are different simple games with the same swing table.
-/

/-- Fried's Example 10.1 (arXiv:2607.07013): the simple games on five players with minimal winning coalitions {123, 024, 034, 134} and {012, 034, 134, 234} are different but have the same swing table. -/
theorem exists_simple_games_ne_of_swing_table_eq :
    ∃ f g : Finset (Fin 5) → Bool, is_simple_game f ∧ is_simple_game g ∧
      (∀ i k, swing_table f i k = swing_table g i k) ∧ f ≠ g := by
  refine ⟨fun S => decide ({1, 2, 3} ⊆ S ∨ {0, 2, 4} ⊆ S ∨ {0, 3, 4} ⊆ S ∨ {1, 3, 4} ⊆ S),
    fun S => decide ({0, 1, 2} ⊆ S ∨ {0, 3, 4} ⊆ S ∨ {1, 3, 4} ⊆ S ∨ {2, 3, 4} ⊆ S),
    ⟨?_, by decide, by decide⟩, ⟨?_, by decide, by decide⟩, ?_, ?_⟩
  · intro S T hST hS
    simp only [decide_eq_true_eq] at hS ⊢
    rcases hS with h | h | h | h
    exacts [Or.inl (h.trans hST), Or.inr (Or.inl (h.trans hST)),
      Or.inr (Or.inr (Or.inl (h.trans hST))), Or.inr (Or.inr (Or.inr (h.trans hST)))]
  · intro S T hST hS
    simp only [decide_eq_true_eq] at hS ⊢
    rcases hS with h | h | h | h
    exacts [Or.inl (h.trans hST), Or.inr (Or.inl (h.trans hST)),
      Or.inr (Or.inr (Or.inl (h.trans hST))), Or.inr (Or.inr (Or.inr (h.trans hST)))]
  · intro i k
    rcases Nat.lt_or_ge 5 k with hk | hk
    · rw [swing_table_eq_zero_of_lt _ i k hk, swing_table_eq_zero_of_lt _ i k hk]
    · interval_cases k <;> revert i <;> decide +kernel
  · intro h
    have := congrFun h {1, 2, 3}
    revert this
    decide
