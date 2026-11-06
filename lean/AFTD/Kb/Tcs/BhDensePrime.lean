import AFTD.Prelude

/-!
# bh_dense_prime

Topic: combinatorics   Node: 5123c238e813

Provenance: helper lemma. step towards infinite_bh_set_upper_density_eq_one_div_h

The prime used for the next block of the construction: a prime larger than both `h` and `h*n`, chosen arbitrarily (`Classical.choose`) from the infinitude of primes.
-/

/-- A prime exceeding `max h (h*n)`. -/
noncomputable def bh_dense_prime (h n : ℕ) : ℕ := Classical.choose (Nat.exists_infinite_primes (max h (h * n) + 1))
