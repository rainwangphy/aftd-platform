import AFTD.Prelude

/-!
# moebius_odd_squarefree_identity_two_pow

Topic: elementary_number_theory   Node: bb2a42934a6a

Provenance: helper lemma. arXiv:2611.05898, An Asymptotic for E. P. Stein Numbers, Proposition 4.2

For any natural number $a$, the sum of the Möbius function $\mu(k)$ over all divisors $k$ of $2^a$ such that $k^2$ divides $2^a$ and $k$ is odd is equal to $1$.
-/

open Finset in
/-- The odd square divisor Möbius sum for powers of 2 is equal to 1. -/
theorem moebius_odd_squarefree_identity_two_pow (a : ℕ) :
    (∑ k ∈ (Nat.divisors (2 ^ a)).filter (fun k => k ^ 2 ∣ 2 ^ a ∧ Odd k), ArithmeticFunction.moebius k) = 1 := by
  have h_set : (Nat.divisors (2 ^ a)).filter (fun k => k ^ 2 ∣ 2 ^ a ∧ Odd k) = {1} := by
    ext k
    simp only [mem_filter, Nat.mem_divisors, mem_singleton]
    constructor
    · rintro ⟨⟨hk_dvd, _⟩, _, hk_odd⟩
      obtain ⟨j, _, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hk_dvd
      cases j with
      | zero => rfl
      | succ j =>
        exfalso
        have heven : Even (2 ^ (j + 1)) := by
          rw [pow_succ']
          exact even_two_mul (2 ^ j)
        exact Nat.not_even_iff_odd.mpr hk_odd heven
    · rintro rfl
      exact ⟨⟨one_dvd _, pow_ne_zero a two_ne_zero⟩, one_dvd _, odd_one⟩
  rw [h_set]
  simp
