import AFTD.Prelude

/-!
# exists_infinite_primes_mod_three_two_and_mod_m_one

Topic: information   Node: f9caec705c29

Provenance: helper lemma. arXiv:2611.07607 Section 4.1

For any natural number $m \ge 2$ with $m \equiv 2 \pmod 3$, there are infinitely many primes $p$ such that $p \equiv 2 \pmod 3$, $p \equiv 1 \pmod m$, and $p \ge 3m + 2$.
-/

/-- There are infinitely many primes congruent to 2 mod 3 and 1 mod m that are at least 3m + 2. -/
theorem exists_infinite_primes_mod_three_two_and_mod_m_one (m : ℕ) (hm : 2 ≤ m) (hm3 : m % 3 = 2) :
    {p : ℕ | Nat.Prime p ∧ p % 3 = 2 ∧ p % m = 1 ∧ 3 * m + 2 ≤ p}.Infinite := by
  have hcoprime : (2 * m + 1).Coprime (3 * m) := by
    rw [Nat.coprime_mul_iff_right]
    refine ⟨?_, ?_⟩
    · change (2 * m + 1).gcd 3 = 1
      rw [Nat.gcd_comm, Nat.gcd_rec]
      have h : (2 * m + 1) % 3 = 2 := by omega
      rw [h]
      decide
    · rw [mul_comm, Nat.coprime_mul_left_add_left]
      exact Nat.coprime_one_left m
  have hne : 3 * m ≠ 0 := by omega
  have hinf : {p : ℕ | Nat.Prime p ∧ p ≡ 2 * m + 1 [MOD 3 * m]}.Infinite :=
    Nat.infinite_setOfPred_prime_and_modEq hne hcoprime
  have hinf_diff : ({p : ℕ | Nat.Prime p ∧ p ≡ 2 * m + 1 [MOD 3 * m]} \ {p : ℕ | p < 3 * m + 2}).Infinite :=
    hinf.sdiff (Set.finite_lt_nat (3 * m + 2))
  apply Set.Infinite.mono (s := {p : ℕ | Nat.Prime p ∧ p ≡ 2 * m + 1 [MOD 3 * m]} \ {p : ℕ | p < 3 * m + 2}) _ hinf_diff
  rintro p ⟨⟨hp, hmod⟩, hnotlt⟩
  refine ⟨hp, ?_, ?_, ?_⟩
  · have h3 : p ≡ 2 * m + 1 [MOD 3] := hmod.of_dvd (dvd_mul_right 3 m)
    change p % 3 = (2 * m + 1) % 3 at h3
    omega
  · have hm' : p ≡ 2 * m + 1 [MOD m] := hmod.of_dvd (dvd_mul_left m 3)
    change p % m = (2 * m + 1) % m at hm'
    rw [hm']
    have : 2 * m + 1 = 1 + m * 2 := by omega
    rw [this, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  · exact not_lt.mp hnotlt
