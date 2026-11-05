import AFTD.Prelude
import AFTD.Kb.NumberTheory.DesignatedOddPartitionGenFun

/-!
# designated_odd_partition_k_tuple

Topic: elementary_number_theory   Node: 9fb2c919b696

Provenance: formalization of a published result. Source: arXiv:2611.05623, Definition 2.1

The number B_k(n) of ordered k-tuples of partitions with designated summands in which all parts are odd, of total size n, defined as the n-th coefficient of G^k.
-/

/-- Number of ordered k-tuples of designated odd partitions of size n. -/
noncomputable def designated_odd_partition_k_tuple (k n : ℕ) : ℕ := PowerSeries.coeff n (designated_odd_partition_gen_fun ^ k)
