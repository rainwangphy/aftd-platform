import AFTD.Prelude
import AFTD.Kb.Tcs.TsallisH

/-!
# tsallis_c3

Topic: information   Node: 1b453c012b27

Provenance: formalization of a published result. Source: OP-1104

The 3-bit majority order-7/8 stability constant C_3(rho) is defined as h((3*rho - rho^3)/2) + 3*h((rho + rho^3)/2) - 4*h(rho) with alpha = 7/8.
-/

/-- Three-bit majority stability constant C_3(rho) for order 7/8. -/
noncomputable def tsallis_c3 (ρ : ℝ) : ℝ := tsallis_h (7 / 8) ((3 * ρ - ρ ^ 3) / 2) +
  3 * tsallis_h (7 / 8) ((ρ + ρ ^ 3) / 2) -
  4 * tsallis_h (7 / 8) ρ
