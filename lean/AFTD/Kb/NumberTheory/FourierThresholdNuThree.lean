import AFTD.Prelude
import AFTD.Kb.NumberTheory.FourierThresholdNu

/-!
# fourier_threshold_nu_three

Topic: elementary_number_theory   Node: 9a41c19556a1

Provenance: formalization of a published result. Source: arXiv:2610.38447, Section 5

The Fourier threshold nu(3) for functions from (ZMod 2)^3 to ZMod 3 with unique zero at 0 is equal to 5.
-/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
lemma fourier_threshold_nu_three_aux : fourier_threshold_nu 3 = 5 := rfl

/-- Evaluation of the Fourier threshold nu(3) = 5. -/
theorem fourier_threshold_nu_three : fourier_threshold_nu 3 = 5 := fourier_threshold_nu_three_aux
