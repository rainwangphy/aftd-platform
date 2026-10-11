import AFTD.Prelude
import AFTD.Kb.NumberTheory.NatPrimePowerParts

/-!
# nat_prime_power_parts_one

Topic: elementary_number_theory   Node: 32b7955c2715

Provenance: helper lemma. Sanity lemma for nat_prime_power_parts (arXiv:2610.11098 (An improved lower bound for separating words by permutation automata)).

S(1) = ∅.
-/

theorem nat_prime_power_parts_one : nat_prime_power_parts 1 = ∅ := by
  simp [nat_prime_power_parts]
