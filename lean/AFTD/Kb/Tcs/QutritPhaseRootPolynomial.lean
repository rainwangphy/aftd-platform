import AFTD.Prelude
import AFTD.Kb.Tcs.QutritPhaseRoot

/-!
# qutrit_phase_root_polynomial

Topic: quantum   Node: 4f59d23ddb29

Provenance: helper lemma. Standard qutrit phase-space convention.

An elementary algebraic identity for the qutrit phase root.
-/

theorem qutrit_phase_root_polynomial :
    qutrit_phase_root^2 + qutrit_phase_root + 1 = 0 := by
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;>
    simp [qutrit_phase_root, Complex.mul_re, Complex.mul_im, pow_two] <;>
    nlinarith [hs]
