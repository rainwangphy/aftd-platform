import AFTD.Prelude

/-!
# two_pow_four_ne_one_of_prime_ge_seven

Topic: combinatorics   Node: f5dbc20c91fb

Provenance: helper lemma. arXiv:2610.34758, Lemma 3.1

For every prime $p \ge 7$, $2^4 \ne 1$ in $\mathbb{Z}/p\mathbb{Z}$.
-/

/-- In ZMod p for a prime p ≥ 7, 2^4 ≠ 1. -/
theorem two_pow_four_ne_one_of_prime_ge_seven (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (2 : ZMod p) ^ 4 ≠ 1 := by
  intro h
  have h1 : ((15 : ℕ) : ZMod p) = 0 := by
    calc ((15 : ℕ) : ZMod p) = (2 : ZMod p) ^ 4 - 1 := by norm_num
    _ = 1 - 1 := by rw [h]
    _ = 0 := sub_self 1
  rw [ZMod.natCast_eq_zero_iff] at h1
  have hp_pr : p.Prime := Fact.out
  have h15 : 15 = 3 * 5 := by norm_num
  rw [h15] at h1
  rcases hp_pr.dvd_mul.mp h1 with h3 | h5
  · have : p ≤ 3 := Nat.le_of_dvd (by norm_num) h3
    omega
  · have : p ≤ 5 := Nat.le_of_dvd (by norm_num) h5
    omega
