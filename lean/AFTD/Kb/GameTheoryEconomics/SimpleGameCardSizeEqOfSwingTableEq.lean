import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsSimpleGame
import AFTD.Kb.GameTheoryEconomics.SwingTable
import AFTD.Kb.GameTheoryEconomics.SumSwingTableEq

/-!
# simple_game_card_size_eq_of_swing_table_eq

Topic: general_equilibrium   Node: 0bae074fbad0

If two simple games have the same swing table, then for every k they have the same number of winning coalitions of size k.
-/

/-- Two simple games with the same swing table have the same number of winning coalitions of each size. -/
theorem simple_game_card_size_eq_of_swing_table_eq {n : ℕ} (f g : Finset (Fin n) → Bool)
    (hf : is_simple_game f) (hg : is_simple_game g)
    (h : ∀ i k, swing_table f i k = swing_table g i k) (k : ℕ) :
    (Finset.univ.filter fun S : Finset (Fin n) => S.card = k ∧ f S = true).card
      = (Finset.univ.filter fun S : Finset (Fin n) => S.card = k ∧ g S = true).card := by
  induction k with
  | zero =>
    have e : ∀ v : Finset (Fin n) → Bool, v ∅ = false →
        (Finset.univ.filter fun S : Finset (Fin n) => S.card = 0 ∧ v S = true) = ∅ := by
      intro v hv
      ext S
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.card_eq_zero, Finset.notMem_empty, iff_false, not_and]
      rintro rfl
      simp [hv]
    rw [e f hf.2.1, e g hg.2.1]
  | succ k ih =>
    have hs : ∑ i, (swing_table f i k : ℝ) = ∑ i, (swing_table g i k : ℝ) := by simp [h]
    rw [sum_swing_table_eq f hf.1 k, sum_swing_table_eq g hg.1 k, ih] at hs
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    have h2 : ((k : ℝ) + 1) * ((Finset.univ.filter fun S : Finset (Fin n) => S.card = k + 1 ∧ f S = true).card : ℝ)
        = ((k : ℝ) + 1) * ((Finset.univ.filter fun S : Finset (Fin n) => S.card = k + 1 ∧ g S = true).card : ℝ) := by
      linarith
    exact_mod_cast mul_left_cancel₀ hk h2
