import AFTD.Prelude
import AFTD.Kb.Tcs.TimelyBin
import AFTD.Kb.Tcs.TimelyItem

/-!
# timely_bin_is_valid

Topic: online_algorithms   Node: efdff3271af5

Provenance: formalization of a published result. Source: arXiv:2611.09611, Section 1.1

A timely bin `b : TimelyBin` is valid, written `timely_bin_is_valid b`, if for every item `p ∈ b.items` the packing time `b.time` satisfies `p.arrival ≤ b.time ∧ b.time ≤ p.deadline`, and the sum of sizes of items in `b.items` is at most 1.
-/

/-- A timely bin is valid if its packing time lies in every item's interval and total size is at most 1. -/
def timely_bin_is_valid (b : TimelyBin) : Prop :=
  (∀ p ∈ b.items, p.arrival ≤ b.time ∧ b.time ≤ p.deadline) ∧
  (∑ p ∈ b.items, p.size) ≤ 1
