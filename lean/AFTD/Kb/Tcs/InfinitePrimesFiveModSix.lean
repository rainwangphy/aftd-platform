import AFTD.Prelude

/-!
# infinite_primes_five_mod_six

Topic: information   Node: 33f2e3bcaab3

Provenance: helper lemma. arXiv:2611.07607, proof of Corollary 1.3

There are infinitely many prime numbers p such that p ≡ 5 [MOD 6].
-/

/-- There are infinitely many primes congruent to 5 modulo 6. -/
lemma infinite_primes_five_mod_six : {p : ℕ | Nat.Prime p ∧ p ≡ 5 [MOD 6]}.Infinite := Nat.infinite_setOfPred_prime_and_modEq (by decide) (by decide)
