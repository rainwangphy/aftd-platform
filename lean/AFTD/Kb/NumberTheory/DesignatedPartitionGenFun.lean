import AFTD.Prelude

/-!
# designated_partition_gen_fun

Topic: elementary_number_theory   Node: 8721ab759554

Provenance: formalization of a published result. Source: arXiv:2611.05623, Section 2, Definition 2.1

The generating function F in PowerSeries ℕ for partitions with designated summands, defined via Nat.Partition.genFun.
-/

/-- Generating function F for partitions with designated summands. -/
noncomputable def designated_partition_gen_fun : PowerSeries ℕ := Nat.Partition.genFun fun _ c => c
