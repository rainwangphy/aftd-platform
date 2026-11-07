import AFTD.Prelude

/-!
# designated_odd_partition_weight

Topic: elementary_number_theory   Node: 290b59bf18ff

Provenance: formalization of a published result. Source: arXiv:2611.05623, Section 2

The character weighting odd parts with their multiplicity and even parts with zero in partitions with designated summands.
-/

/-- The weight assigned to part i occurring c times for designated partitions with all parts odd. -/
def designated_odd_partition_weight (i c : ℕ) : ℕ := if i % 2 = 1 then c else 0
