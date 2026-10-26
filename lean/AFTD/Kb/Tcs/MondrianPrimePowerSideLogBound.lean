import AFTD.Prelude

/-!
# mondrian_prime_power_side_log_bound

Topic: combinatorics   Node: f4a85d6bbd58

Provenance: helper lemma. Helper for OP-280 and mondrian_no_perfect_prime_mul_prime_pow. Related work: arXiv:2610.19193, Section 1 (the zero-defect question); arXiv:2007.09639, Theorem 4.1 (prime-power and small prime-product exclusions).

A pure p-power side fitting in a q times p^e square has exponent at most e plus floor(log_p(q)).
-/

theorem mondrian_prime_power_side_log_bound (p q e a : ℕ) (hp : Nat.Prime p)
    (h : p ^ a ≤ q * p ^ e) : a ≤ e + Nat.log p q := by
  have hh := h.trans_lt (Nat.mul_lt_mul_of_pos_right
    (Nat.lt_pow_succ_log_self hp.one_lt q) (pow_pos hp.pos e))
  rw [← pow_add] at hh
  have := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hh
  omega
