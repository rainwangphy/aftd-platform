import AFTD.Prelude
import AFTD.Kb.Tcs.RealErf

/-!
# c_G

Topic: information   Node: 464d71c10346

Provenance: formalization of a published result. Source: OP-797

For a real number ρ, the Gaussian majority limit stability constant c_G(ρ) : ℝ is defined as 2 * ((∫ g, Real.sqrt (1 - (real_erf (ρ * g / Real.sqrt (2 * (1 - ρ ^ 2)))) ^ 2) ∂(ProbabilityTheory.gaussianReal 0 1)) - Real.sqrt (1 - ρ ^ 2)).
-/

open MeasureTheory ProbabilityTheory in
/-- The Gaussian majority limit stability constant c_G(rho). -/
noncomputable def c_G (ρ : ℝ) : ℝ := 2 * ((∫ g, Real.sqrt (1 - (real_erf (ρ * g / Real.sqrt (2 * (1 - ρ ^ 2)))) ^ 2) ∂(ProbabilityTheory.gaussianReal 0 1)) -
       Real.sqrt (1 - ρ ^ 2))
