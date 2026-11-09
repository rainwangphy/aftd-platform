import AFTD.Prelude
import AFTD.Kb.NumberTheory.DesignatedPartitionKTuple
import AFTD.Kb.NumberTheory.DesignatedPartitionSixTupleTwentyTwoNotMod729

/-!
# designated_partition_six_tuple_not_all_mod_729

Topic: elementary_number_theory   Node: ce4bb8b56839

Provenance: helper lemma. arXiv:2611.05623 Conjecture 6.3

It is not the case that for all natural numbers n, 729 divides the number of designated partition 6-tuples of size 12n + 10, designated_partition_k_tuple 6 (12 * n + 10).
-/

/-- 729 does not divide designated_partition_k_tuple 6 (12n + 10) for all natural numbers n. -/
theorem designated_partition_six_tuple_not_all_mod_729 :
    ¬ (∀ n : ℕ, 729 ∣ designated_partition_k_tuple 6 (12 * n + 10)) := by
  intro h
  have h1 := h 1
  norm_num at h1
  exact designated_partition_six_tuple_twenty_two_not_mod_729 h1
