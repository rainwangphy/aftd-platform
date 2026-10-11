import AFTD.Prelude
import AFTD.Kb.NumberTheory.NatPrimePowerParts

/-!
# nat_prime_power_parts_prime_pow

Topic: elementary_number_theory   Node: eff80c303e5c

Provenance: helper lemma. Sanity lemma for nat_prime_power_parts (arXiv:2610.11098 (An improved lower bound for separating words by permutation automata)).

For a prime p and k ≥ 1, S(p^k) = {p^k}.
-/

theorem nat_prime_power_parts_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    nat_prime_power_parts (p ^ k) = {p ^ k} := by
  unfold nat_prime_power_parts
  rw [Nat.primeFactors_prime_pow hk hp]
  simp [Nat.factorization_pow, hp.factorization_self]
