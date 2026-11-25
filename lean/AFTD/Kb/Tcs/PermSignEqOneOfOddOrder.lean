import AFTD.Prelude

/-!
# perm_sign_eq_one_of_odd_order

Topic: combinatorics   Node: 2e0b45762205

Provenance: helper lemma. arXiv:2611.29409 Lemma 3.1 proof

For any finite type α and any permutation σ of α, if the order of σ is odd, then the sign of σ is 1.
-/

/-- A permutation of odd order has sign 1. -/
theorem perm_sign_eq_one_of_odd_order {α : Type*} [DecidableEq α] [Fintype α] (σ : Equiv.Perm α) (h : Odd (orderOf σ)) : Equiv.Perm.sign σ = 1 := by
  have h1 : (Equiv.Perm.sign σ) ^ (orderOf σ) = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h2 | h2
  · exact h2
  · rw [h2, h.neg_one_pow] at h1
    norm_num at h1
