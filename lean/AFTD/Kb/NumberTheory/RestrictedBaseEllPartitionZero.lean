import AFTD.Prelude
import AFTD.Kb.NumberTheory.RestrictedBaseEllPartition

/-!
# restricted_base_ell_partition_zero

Topic: elementary_number_theory   Node: e6bf5b6ee176

Provenance: helper lemma. arXiv:2611.08109 Section 1

For any natural numbers $k$ and $\ell$, the restricted base-$\ell$ partition function evaluated at 0 is 1.
-/

/-- The restricted base-ℓ partition function at 0 is 1. -/
theorem restricted_base_ell_partition_zero (k ℓ : ℕ) :
    restricted_base_ell_partition k ℓ 0 = 1 := by
  simp [restricted_base_ell_partition, Nat.Partition.restricted, Nat.Partition.countRestricted]
