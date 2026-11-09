import AFTD.Prelude

/-!
# designated_partition_a

Topic: elementary_number_theory   Node: 30572014d0ca

Provenance: formalization of a published result. Source: arXiv:2611.05623 Definition 2.1 -- Partitions with designated summands: k-tuples and their congruences

For natural numbers k and n, the integer value `designated_partition_a k n` is defined as `PowerSeries.coeff n ((Nat.Partition.genFun (fun _ c ↦ (c : ℤ))) ^ k)`, the n-th coefficient in PowerSeries ℤ of the k-th power of the partition generating function `Nat.Partition.genFun` with multiplicity weight `fun _ c ↦ (c : ℤ)`.
-/

/-- The integer coefficient A_k(n) of q^n in F^k for k-tuples of designated partitions. -/
noncomputable def designated_partition_a (k : ℕ) (n : ℕ) : ℤ := PowerSeries.coeff n ((Nat.Partition.genFun (fun _ c ↦ (c : ℤ))) ^ k)
