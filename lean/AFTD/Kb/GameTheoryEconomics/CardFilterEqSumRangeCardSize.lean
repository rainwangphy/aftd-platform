import AFTD.Prelude

/-!
# card_filter_eq_sum_range_card_size

Topic: general_equilibrium   Node: 9be4302debaa

The number of winning coalitions of a game is the sum, over k from 0 to n, of the number of winning coalitions of size k.
-/

/-- The number of winning coalitions is the sum over sizes `k ≤ n` of the number of winning coalitions of size `k`. -/
theorem card_filter_eq_sum_range_card_size {n : ℕ} (v : Finset (Fin n) → Bool) :
    (Finset.univ.filter fun S : Finset (Fin n) => v S = true).card
      = ∑ k ∈ Finset.range (n + 1), (Finset.univ.filter fun S : Finset (Fin n) => S.card = k ∧ v S = true).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Finset.card) (t := Finset.range (n + 1))]
  · apply Finset.sum_congr rfl
    intro k _
    congr 1
    ext S
    simp [and_comm]
  · intro S _
    simp only [Finset.coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le ((Finset.card_le_univ S).trans (by simp))
