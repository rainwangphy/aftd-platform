import AFTD.Prelude
import AFTD.Kb.NumberTheory.LeadingUnitQg

/-!
# leading_unit_ag

Topic: elementary_number_theory   Node: 624622ae3e63

Provenance: formalization of a published result. Source: arXiv:2611.10200, eq. (1.4)

The generating function A_g(z) = 1 / ((1 - z)^2 Q_g(z)) regarded as a formal power series over ℚ.
-/

/-- The generating function A_g(z) = ((1 - z)^2 Q_g(z))⁻¹. -/
noncomputable def leading_unit_ag (g : ℕ) : PowerSeries ℚ :=
  open PowerSeries in
  ((1 - X) ^ 2 * leading_unit_qg g)⁻¹
