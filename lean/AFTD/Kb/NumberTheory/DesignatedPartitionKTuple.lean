import AFTD.Prelude
import AFTD.Kb.NumberTheory.DesignatedPartitionGenFun

/-!
# designated_partition_k_tuple

Topic: elementary_number_theory   Node: f103c882322e

Provenance: formalization of a published result. Source: arXiv:2611.05623, Section 2, Definition 2.1

The number A_k(n) of ordered k-tuples of partitions with designated summands of total size n, defined as the n-th coefficient of F^k.
-/

/-- Number of ordered k-tuples of partitions with designated summands of size n. -/
noncomputable def designated_partition_k_tuple (k n : ℕ) : ℕ := PowerSeries.coeff n (designated_partition_gen_fun ^ k)
