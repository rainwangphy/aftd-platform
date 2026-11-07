import AFTD.Prelude
import AFTD.Kb.NumberTheory.DesignatedOddPartGenFun

/-!
# designated_odd_partition_tuple_coeff

Topic: elementary_number_theory   Node: 69d571d29b99

Provenance: formalization of a published result. Source: arXiv:2611.05623, Definition 2.1

The number B_k(n) of ordered k-tuples of partitions with designated summands in which all parts are odd of total size n, defined as the nth coefficient of the kth power of the odd-part designated partition generating function.
-/

/-- Number B_k(n) of ordered k-tuples of odd-part designated partitions of total size n. -/
noncomputable def designated_odd_partition_tuple_coeff (k n : ℕ) : ℕ := PowerSeries.coeff n (designated_odd_part_gen_fun ^ k)
