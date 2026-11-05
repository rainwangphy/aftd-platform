import AFTD.Prelude

/-!
# designated_odd_partition_character

Topic: elementary_number_theory   Node: b36dcaf7b378

Provenance: formalization of a published result. Source: arXiv:2611.05623, Section 2

The character function assigning multiplicity c to odd part sizes i, and 0 to even part sizes, for partitions into odd parts with designated summands.
-/

/-- Multiplicity character for partitions into odd parts with designated summands. -/
def designated_odd_partition_character (i c : ℕ) : ℕ := if Odd i then c else 0
