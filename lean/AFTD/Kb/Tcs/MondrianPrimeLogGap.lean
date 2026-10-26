import AFTD.Prelude

/-!
# mondrian_prime_log_gap

Topic: combinatorics   Node: c344d6779191

Provenance: helper lemma. Helper for OP-280 and mondrian_no_perfect_prime_mul_prime_pow. Related work: arXiv:2610.19193, Section 1 (the zero-defect question); arXiv:2007.09639, Theorem 4.1 (prime-power and small prime-product exclusions).

For distinct primes p and q, p to floor(log_p(q)) is strictly less than q, q is below the next power, and floor(log_p(q)) plus one is strictly less than q.
-/

theorem mondrian_prime_log_gap (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) :
    p ^ Nat.log p q < q ∧ q < p ^ (Nat.log p q + 1) ∧ Nat.log p q + 1 < q := by
  have hlo := Nat.pow_log_le_self p hq.ne_zero
  have hne : p ^ Nat.log p q ≠ q := by
    intro hh
    exact hpq ((hq.pow_eq_iff.mp hh).1)
  have hlt : p ^ Nat.log p q < q := lt_of_le_of_ne hlo hne
  have hpow : Nat.log p q + 1 ≤ p ^ Nat.log p q := by
    have := Nat.lt_pow_self (n := Nat.log p q) hp.one_lt
    omega
  exact ⟨hlt, Nat.lt_pow_succ_log_self hp.one_lt q, hpow.trans_lt hlt⟩
