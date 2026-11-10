import AFTD.Prelude

/-!
# leading_unit_qg

Topic: elementary_number_theory   Node: d4ae403b71e6

Provenance: formalization of a published result. Source: arXiv:2611.10200, eq. (1.4)

The polynomial Q_g(z) = 1 - ∑_{j=1}^g z^j associated with g leading unit coefficients, regarded as a formal power series over ℚ.
-/

/-- The characteristic polynomial Q_g(z) = 1 - ∑_{j=1}^g z^j for g leading units. -/
noncomputable def leading_unit_qg (g : ℕ) : PowerSeries ℚ :=
  open PowerSeries in
  1 - ∑ j ∈ Finset.Icc 1 g, (X : PowerSeries ℚ) ^ j
