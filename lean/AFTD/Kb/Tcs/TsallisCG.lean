import AFTD.Prelude
import AFTD.Kb.Tcs.TsallisH

/-!
# tsallis_cG

Topic: information   Node: 692cc423c2a9

Provenance: formalization of a published result. Source: OP-1104

The Gaussian majority limit order-7/8 stability constant C_G(rho) is defined as 2 * (E[Phi(rho * Z / sqrt(1 - rho^2))^(7/8)] - h(rho)) where Z is standard normal and Phi is the standard normal cumulative distribution function.
-/

open MeasureTheory ProbabilityTheory in
/-- Gaussian majority limit stability constant C_G(rho) for order 7/8. -/
noncomputable def tsallis_cG (ρ : ℝ) : ℝ := 2 * ((∫ z, (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (ρ * z / Real.sqrt (1 - ρ ^ 2))) ^ (7 / 8 : ℝ) ∂(ProbabilityTheory.gaussianReal 0 1)) -
       tsallis_h (7 / 8) ρ)
