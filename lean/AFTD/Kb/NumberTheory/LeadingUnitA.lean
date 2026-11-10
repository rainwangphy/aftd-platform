import AFTD.Prelude
import AFTD.Kb.NumberTheory.LeadingUnitAg

/-!
# leading_unit_a

Topic: elementary_number_theory   Node: 1f0b862ef8d9

Provenance: formalization of a published result. Source: arXiv:2611.10200, eq. (1.4)

The coefficient a_m^{(g)} of z^m in the formal power series A_g(z) = ((1 - z)^2 Q_g(z))⁻¹.
-/

/-- The m-th coefficient a_m^{(g)} of A_g(z). -/
noncomputable def leading_unit_a (g m : ℕ) : ℚ :=
  PowerSeries.coeff m (leading_unit_ag g)
