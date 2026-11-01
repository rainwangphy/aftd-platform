import AFTD.Prelude
import AFTD.Kb.NumberTheory.FourierThresholdNu

/-!
# fourier_threshold_nu_two

Topic: elementary_number_theory   Node: 49b1b667647c

Provenance: formalization of a published result. Source: arXiv:2610.38447, Section 5

The Fourier threshold nu(2) for functions from (ZMod 2)^2 to ZMod 3 with unique zero at 0 is equal to 3.
-/

/-- Evaluation of the Fourier threshold nu(2) = 3. -/
theorem fourier_threshold_nu_two : fourier_threshold_nu 2 = 3 := rfl
