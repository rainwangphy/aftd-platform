import AFTD.Prelude

/-!
# leading_unit_h

Topic: elementary_number_theory   Node: d3a5bcc9d143

Provenance: formalization of a published result. Source: arXiv:2611.10200, eq. (1.2)-(1.3)

For natural numbers g, k, N : ℕ, the sequence of integers leading_unit_h g k N : ℕ → ℤ associated with coefficient list [1^g, 0^k, N] is defined recursively on ℕ: leading_unit_h g k N 0 = 0, leading_unit_h g k N 1 = 1, and for n ≥ 0, setting L = g + k + 1, if n + 2 ≤ L then leading_unit_h g k N (n + 2) = 1 + ∑ j ∈ Finset.range (min g (n + 1)), leading_unit_h g k N (n + 2 - (j + 1)), and if n + 2 > L then leading_unit_h g k N (n + 2) = (∑ j ∈ Finset.range g, leading_unit_h g k N (n + 2 - (j + 1))) + (N : ℤ) * leading_unit_h g k N (n + 2 - L).
-/

/-- The standard positive linear recurrence sequence associated with coefficient list [1^g, 0^k, N], taking values in ℤ. -/
def leading_unit_h (g k N : ℕ) : ℕ → ℤ
| 0 => 0
| 1 => 1
| n + 2 =>
  let L := g + k + 1
  if n + 2 ≤ L then
    1 + ∑ j ∈ Finset.range (min g (n + 1)), leading_unit_h g k N (n + 2 - (j + 1))
  else
    (∑ j ∈ Finset.range g, leading_unit_h g k N (n + 2 - (j + 1))) + (N : ℤ) * leading_unit_h g k N (n + 2 - L)
termination_by m => m
decreasing_by all_goals omega
