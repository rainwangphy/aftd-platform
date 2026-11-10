import AFTD.Prelude
import AFTD.Kb.Tcs.TimelyBin
import AFTD.Kb.Tcs.TimelyBinIsValid
import AFTD.Kb.Tcs.TimelyItem
import AFTD.Kb.Tcs.InstLinearOrderTimelyItem

/-!
# is_valid_timely_packing

Topic: online_algorithms   Node: b6adb1851c92

Provenance: formalization of a published result. Source: arXiv:2611.09611, Section 1.1

A finite set of bins `P : Finset TimelyBin` is a valid timely packing of an item set `I : Finset TimelyItem`, written `is_valid_timely_packing I P`, if every bin `b ∈ P` is valid (`timely_bin_is_valid b`) and non-empty, the item sets of distinct bins in `P` are pairwise disjoint, and the union of the item sets across all bins in `P` equals `I`.
-/

/-- A set of bins is a valid timely packing of I if every bin is valid and nonempty, bins have disjoint items, and their union is I. -/
def is_valid_timely_packing (I : Finset TimelyItem) (P : Finset TimelyBin) : Prop :=
  open Classical in
  (∀ b ∈ P, timely_bin_is_valid b ∧ b.items.Nonempty) ∧
  (∀ b₁ ∈ P, ∀ b₂ ∈ P, b₁ ≠ b₂ → Disjoint b₁.items b₂.items) ∧
  P.biUnion (fun b => b.items) = I
