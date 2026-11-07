import AFTD.Prelude
import AFTD.Kb.NumberTheory.DesignatedOddPartitionWeight

/-!
# designated_odd_part_gen_fun

Topic: elementary_number_theory   Node: 036793c4ce24

Provenance: formalization of a published result. Source: arXiv:2611.05623, Definition 2.1

The generating function in PowerSeries ℕ for partitions with designated summands in which all parts are odd, equal to Nat.Partition.genFun designated_odd_partition_weight.
-/

/-- Generating function for partitions with designated summands in which all parts are odd. -/
noncomputable def designated_odd_part_gen_fun : PowerSeries ℕ := Nat.Partition.genFun designated_odd_partition_weight
