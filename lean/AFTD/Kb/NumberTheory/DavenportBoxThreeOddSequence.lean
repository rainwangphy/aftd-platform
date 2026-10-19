import AFTD.Prelude

/-!
# davenport_box_three_odd_sequence

Topic: elementary_number_theory   Node: c2c0b0194f27

Provenance: formalization of a published result. Source: arXiv:2610.16562 (The Davenport constant of low-dimensional boxes), Sec. 4, the sequence T(m) for odd m (proof of Theorem 3).

The sequence T(m) for odd m: (-m,-m,-m) repeated 4m^3-8m^2+5m-2 times, (-m,m-1,m) repeated 4m^3-2m^2+2m times, (m,-m,m-2) repeated 4m^3-2m^2+m times and (m-1,m,-m) repeated 4m^3-4m^2+2m times.
-/

/-- The odd-`m` sequence `T(m)` of arXiv:2610.16562 Sec. 4. -/
def davenport_box_three_odd_sequence (m : ℕ) : Multiset (Fin 3 → ℤ) :=
  Multiset.replicate (4 * m ^ 3 - 8 * m ^ 2 + 5 * m - 2) ![-(m : ℤ), -m, -m] +
  Multiset.replicate (4 * m ^ 3 - 2 * m ^ 2 + 2 * m) ![-(m : ℤ), m - 1, m] +
  Multiset.replicate (4 * m ^ 3 - 2 * m ^ 2 + m) ![(m : ℤ), -m, m - 2] +
  Multiset.replicate (4 * m ^ 3 - 4 * m ^ 2 + 2 * m) ![(m : ℤ) - 1, m, -m]
