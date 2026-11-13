import AFTD.Prelude

/-!
# chunk_inner_token_bound_le

Topic: approximation   Node: 071a57735262

Provenance: helper lemma. arXiv:2611.15074, Lemma 3.8 proof

For l ≤ M and natural numbers q and M, (⌈l / q⌉ - 1) + (q - 1) is at most q - 1 + ⌈M / q⌉.
-/

/-- Arithmetic inequality (⌈l / q⌉ - 1) + (q - 1) ≤ q - 1 + ⌈M / q⌉ for Case 2 of Lemma 3.8. -/
theorem chunk_inner_token_bound_le (M q l : ℕ) (hl : l ≤ M) :
    (l ⌈/⌉ q - 1) + (q - 1) ≤ q - 1 + M ⌈/⌉ q := by
  have h : l ⌈/⌉ q ≤ M ⌈/⌉ q := by
    rw [Nat.ceilDiv_eq_add_pred_div, Nat.ceilDiv_eq_add_pred_div]
    exact Nat.div_le_div_right (by omega)
  omega
