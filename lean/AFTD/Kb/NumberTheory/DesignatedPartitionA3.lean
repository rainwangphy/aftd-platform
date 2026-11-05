import AFTD.Prelude

/-!
# designated_partition_a3

Topic: elementary_number_theory   Node: 82f3b74b6c01

Provenance: formalization of a published result. Source: arXiv:2611.05623 Proposition 3.13

The function mapping each natural number k to the natural number k * (k + 1) * (k + 14) / 6.
-/

/-- The polynomial formula for A_k(3) = k(k+1)(k+14)/6. -/
def designated_partition_a3 (k : ℕ) : ℕ := k * (k + 1) * (k + 14) / 6
