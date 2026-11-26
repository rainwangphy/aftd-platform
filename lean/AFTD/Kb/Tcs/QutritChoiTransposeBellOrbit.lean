import AFTD.Prelude
import AFTD.Kb.Tcs.QutritConvolutionChoi
import AFTD.Kb.Tcs.QutritBobTranspose
import AFTD.Kb.Tcs.QutritBellOrbitSlice

/-!
# qutrit_choi_transpose_bell_orbit

Topic: quantum   Node: f831282fed8c

Provenance: helper lemma. OP-2299; qutrit convolution, experiments 40125-40126 and 40163-40166.

An exact identity in the qutrit Bell-orbit and real witness reduction.
-/

theorem qutrit_choi_transpose_bell_orbit (σ : Matrix (Fin 3) (Fin 3) ℂ) :
    qutrit_bell_orbit_slice (qutrit_bob_transpose (qutrit_convolution_choi σ)) := by
  have hsum (a b c d : Fin 3) : a+d=c+b ↔ b-a=d-c := by
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide
  have hshift (a b c d : Fin 3) : (a+1)+(d+1)=(c+1)+(b+1) ↔ a+d=c+b := by
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide
  have hsub (x y : Fin 3) : (x+1)-(y+1)=x-y := by
    fin_cases x <;> fin_cases y <;> decide
  constructor
  · intro a b c d h
    simp [qutrit_bob_transpose, qutrit_convolution_choi, hsum, h]
  · intro a b c d
    simp only [qutrit_bob_transpose, Matrix.of_apply, qutrit_convolution_choi]
    simp [hshift, hsub]
