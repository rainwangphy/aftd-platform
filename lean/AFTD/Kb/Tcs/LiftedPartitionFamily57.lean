import AFTD.Prelude
import AFTD.Kb.Tcs.PartitionA
import AFTD.Kb.Tcs.PartitionLift57

/-!
# lifted_partition_family_57

Topic: combinatorics   Node: 4ed0ad0707bd

Provenance: formalization of a published result. Source: arXiv:2610.01747, Corollary 6.2

For t ≥ 1, the lifted family of partitions of t + 56 obtained by adding t - 1 ones to each partition in A_57.
-/

/-- The lifted counterexample family {λ ⊎ 1^(t-1) : λ ∈ A_57} in P_{t+56}. -/
def lifted_partition_family_57 (t : ℕ) (ht : 1 ≤ t) : Finset (Nat.Partition (t + 56)) := (partition_A 57).image (partition_lift_57 t ht)
