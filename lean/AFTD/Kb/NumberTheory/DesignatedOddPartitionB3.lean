import AFTD.Prelude

/-!
# designated_odd_partition_b3

Topic: elementary_number_theory   Node: e8376eaefe44

Provenance: formalization of a published result. Source: arXiv:2611.05623, Theorem 4.5(c) and Section 6

The function designated_odd_partition_b3 mapping each natural number k to the natural number k * (k + 2) * (k + 7) / 6.
-/

/-- Arithmetic function computing k * (k + 2) * (k + 7) / 6 for odd-part designated partition k-tuples. -/
def designated_odd_partition_b3 (k : ℕ) : ℕ := k * (k + 2) * (k + 7) / 6
