import AFTD.Prelude
import AFTD.Kb.NumberTheory.DesignatedPartitionKTuple
import AFTD.Kb.NumberTheory.DesignatedPartitionSixTupleTwentyTwoNotMod729

/-!
# designated_partition_six_tuple_exact_valuation_iff

Topic: elementary_number_theory   Node: 17a3a89bb992

Provenance: helper lemma. arXiv:2611.05623 Conjecture 6.3

The exact 3-adic valuation statement that 243 divides designated_partition_k_tuple 6 (12n + 10) for all n and 729 does not divide all of them is logically equivalent to the universal divisibility by 243 alone.
-/

/-- The conjunction of universal divisibility by 243 and non-universal divisibility by 729 is equivalent to universal divisibility by 243. -/
theorem designated_partition_six_tuple_exact_valuation_iff :
    ((∀ n : ℕ, 243 ∣ designated_partition_k_tuple 6 (12 * n + 10)) ∧
     ¬(∀ n : ℕ, 729 ∣ designated_partition_k_tuple 6 (12 * n + 10))) ↔
    (∀ n : ℕ, 243 ∣ designated_partition_k_tuple 6 (12 * n + 10)) := by
  constructor
  · rintro ⟨h1, -⟩
    exact h1
  · intro h1
    refine ⟨h1, ?_⟩
    intro h2
    exact designated_partition_six_tuple_twenty_two_not_mod_729 (h2 1)
