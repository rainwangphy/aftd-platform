import AFTD.Prelude
import AFTD.Kb.Tcs.QutritConvolutionChoi
import AFTD.Kb.Tcs.QutritBobTranspose
import AFTD.Kb.Tcs.QutritBellOrbitInverse

/-!
# qutrit_bell_orbit_inverse_choi

Topic: quantum   Node: 10f7319a7e62

Provenance: helper lemma. OP-2299; qutrit convolution, experiments 40125-40126 and 40163-40166.

An exact identity in the qutrit Bell-orbit and real witness reduction.
-/

theorem qutrit_bell_orbit_inverse_choi (σ : Matrix (Fin 3) (Fin 3) ℂ) :
    qutrit_bell_orbit_inverse (qutrit_bob_transpose (qutrit_convolution_choi σ)) = σ := by
  have hn (i : Fin 3) : -i-i=i := by fin_cases i <;> decide
  ext i j
  simp [qutrit_bell_orbit_inverse, qutrit_bob_transpose, qutrit_convolution_choi, hn]
  ring
