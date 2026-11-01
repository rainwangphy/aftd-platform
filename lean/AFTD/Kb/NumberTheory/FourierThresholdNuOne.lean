import AFTD.Prelude
import AFTD.Kb.NumberTheory.FourierThresholdNu

/-!
# fourier_threshold_nu_one

Topic: elementary_number_theory   Node: b99ccf385ba4

Provenance: formalization of a published result. Source: arXiv:2610.38447, Section 5

The Fourier threshold nu(1) for functions from ZMod 2 to ZMod 3 with unique zero at 0 is equal to 2.
-/

/-- Evaluation of the Fourier threshold nu(1) = 2. -/
theorem fourier_threshold_nu_one : fourier_threshold_nu 1 = 2 := rfl
