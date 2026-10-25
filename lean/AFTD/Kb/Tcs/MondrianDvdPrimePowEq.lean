import AFTD.Prelude

/-!
# mondrian_dvd_prime_pow_eq

Topic: combinatorics   Node: 8b5c64320c17

Provenance: helper lemma. Helper for OP-280 and mondrian_perfect_partition_large_prime_iff. Related work: arXiv:2610.19193, Section 1 (perfect partitions and scaling); arXiv:2007.09639, Theorem 4.1 (available shapes and prime-power exclusions).

A divisor x of a power of a prime p is p to its own p-adic exponent.
-/

theorem mondrian_dvd_prime_pow_eq (p e x : ℕ) (hp : Nat.Prime p)
    (hx : x ∣ p ^ e) : x = p ^ (x.factorization p) := by
  obtain ⟨u, hu, rfl⟩ := (Nat.dvd_prime_pow hp).mp hx
  rw [Nat.factorization_pow_self hp]
