import AFTD.Prelude
import AFTD.Kb.NumberTheory.DesignatedOddPartitionCharacter

/-!
# designated_odd_partition_gen_fun

Topic: elementary_number_theory   Node: 397735e03d09

Provenance: formalization of a published result. Source: arXiv:2611.05623, Definition 2.1

The generating function G in PowerSeries Nat for partitions with designated summands in which all parts are odd, defined via Nat.Partition.genFun.
-/

/-- Generating function for partitions with designated summands into odd parts. -/
noncomputable def designated_odd_partition_gen_fun : PowerSeries ℕ := Nat.Partition.genFun designated_odd_partition_character
