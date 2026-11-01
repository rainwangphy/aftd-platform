import AFTD.Prelude

/-!
# c_3

Topic: information   Node: 7ea8fd2a02f5

Provenance: formalization of a published result. Source: OP-797

The 3-bit majority Hellinger stability constant c_3(rho) is defined as sqrt(1 - ((3*rho - rho^3)/2)^2) + 3*sqrt(1 - ((rho + rho^3)/2)^2) - 4*sqrt(1 - rho^2).
-/

/-- The 3-bit majority stability constant c_3(rho). -/
noncomputable def c_3 (ρ : ℝ) : ℝ := Real.sqrt (1 - ((3 * ρ - ρ ^ 3) / 2) ^ 2) +
  3 * Real.sqrt (1 - ((ρ + ρ ^ 3) / 2) ^ 2) -
  4 * Real.sqrt (1 - ρ ^ 2)
