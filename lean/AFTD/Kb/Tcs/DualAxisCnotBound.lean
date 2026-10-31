import AFTD.Prelude

/-!
# dual_axis_cnot_bound

Topic: quantum   Node: b732879cf8d4

Provenance: formalization of a published result. Source: scout/2610-04621-exact-clifford-optimality-for-two-sided-locally-randomized.md:1658

The dual-axis CNOT upper bound of arXiv:2610.04621 Eq. (78): 3k - 5 for odd k, and 3k - 6 for even k.
-/

/-- The dual-axis CNOT upper bound of arXiv:2610.04621 Eq. (78). -/
def dual_axis_cnot_bound (k : ℕ) : ℕ := if k % 2 = 1 then 3 * k - 5 else 3 * k - 6
