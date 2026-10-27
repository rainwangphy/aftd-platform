import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.HungerTransientTime
import AFTD.Kb.GameTheoryEconomics.HungerRecurrentBasin
import AFTD.Kb.GameTheoryEconomics.HungerIter

/-!
# hunger_transient_time_eq_zero_of_mem_basin

Topic: combinatorial_games   Node: 24edb5265af6

Provenance: helper lemma. arXiv:2610.08949 after Thm 3.8

For a natural number n with [NeZero n], a rational matrix P : Matrix (Fin n) (Fin n) ℚ, a natural number T, and a rational vector h : Fin n → ℚ, if h belongs to hunger_recurrent_basin P T, then hunger_transient_time P T h = 0.
-/

/-- For a vector already in the recurrent basin, the transient hitting time is zero. -/
theorem hunger_transient_time_eq_zero_of_mem_basin {n : ℕ} [NeZero n]
    (P : Matrix (Fin n) (Fin n) ℚ) (T : ℕ) (h : Fin n → ℚ)
    (h_mem : h ∈ hunger_recurrent_basin P T) :
    hunger_transient_time P T h = 0 := by
  have h0 : (0 : ℕ) ∈ {t : ℕ | hunger_iter P t h ∈ hunger_recurrent_basin P T} := by
    change hunger_iter P 0 h ∈ hunger_recurrent_basin P T
    dsimp [hunger_iter]
    exact h_mem
  have hle : hunger_transient_time P T h ≤ 0 := by
    dsimp [hunger_transient_time]
    exact Nat.sInf_le h0
  omega
