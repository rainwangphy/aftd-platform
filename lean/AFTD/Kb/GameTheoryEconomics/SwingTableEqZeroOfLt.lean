import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SwingTable

/-!
# swing_table_eq_zero_of_lt

Topic: general_equilibrium   Node: b8ffbe6e1fdc

In a game on n players, T(i, k) = 0 whenever k > n.
-/

/-- A swing table vanishes at sizes larger than the number of players. -/
theorem swing_table_eq_zero_of_lt {n : ℕ} (v : Finset (Fin n) → Bool) (i : Fin n) (k : ℕ)
    (hk : n < k) : swing_table v i k = 0 := by
  unfold swing_table
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro S _ h
  have := Finset.card_le_univ S
  simp only [Fintype.card_fin] at this
  omega
