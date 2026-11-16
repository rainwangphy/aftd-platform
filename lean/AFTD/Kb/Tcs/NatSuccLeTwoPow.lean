import AFTD.Prelude

/-!
# nat_succ_le_two_pow

Topic: online_algorithms   Node: 9c6532ce7786

Provenance: helper lemma. arXiv:2611.17090, Lemma 7 proof

For every natural number j, (j + 1 : ℝ) ≤ 2^j.
-/

/-- Linear bound by dyadic powers: j + 1 ≤ 2^j for all natural numbers j. -/
lemma nat_succ_le_two_pow (j : ℕ) : (j + 1 : ℝ) ≤ (2 : ℝ) ^ j := by
  exact_mod_cast (Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := j)))
