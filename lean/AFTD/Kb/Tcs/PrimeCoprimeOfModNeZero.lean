import AFTD.Prelude

/-!
# prime_coprime_of_mod_ne_zero

Topic: combinatorics   Node: 2e8216b4114c

Provenance: helper lemma. arXiv:2610.24758 Lemma 1 proof

For any prime n and natural number s, if s is not divisible by n (s % n ≠ 0), then s and n are coprime.
-/

/-- A prime n and a natural number s not divisible by n are coprime. -/
theorem prime_coprime_of_mod_ne_zero (n s : ℕ) (hn : n.Prime) (hs : s % n ≠ 0) : Nat.Coprime s n := by
  rw [Nat.coprime_comm]
  rw [hn.coprime_iff_not_dvd]
  rwa [Nat.dvd_iff_mod_eq_zero]
