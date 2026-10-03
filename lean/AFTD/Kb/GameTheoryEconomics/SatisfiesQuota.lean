import AFTD.Prelude

/-!
# satisfies_quota

Topic: social_choice   Node: 717106f2c6b5

Quota: the seats sum to the house size and each state receives the floor or the ceiling of its standard quota h p_i / sum p.
-/

/-- Quota (Gölz, Peters and Procaccia, In This Apportionment Lottery, the House Always Wins, Sec. 2): the seats `a` sum to the house size `h`, and each state `i` gets `⌊q_i⌋` or `⌈q_i⌉` seats, where `q_i = h p_i / Σ_j p_j` is its standard quota. -/
def satisfies_quota {n : ℕ} (p : Fin n → ℕ) (h : ℕ) (a : Fin n → ℕ) : Prop :=
  ∑ i, a i = h ∧ ∀ i, ⌊((h * p i : ℕ) : ℚ) / ((∑ j, p j : ℕ) : ℚ)⌋₊ ≤ a i ∧
    a i ≤ ⌈((h * p i : ℕ) : ℚ) / ((∑ j, p j : ℕ) : ℚ)⌉₊
