import AFTD.Prelude
import AFTD.Kb.Tcs.QutritPhaseRoot

/-!
# qutrit_phase_root_conjugate

Topic: quantum   Node: 3ebab7efbb26

Provenance: helper lemma. Standard qutrit phase-space convention.

An elementary algebraic identity for the qutrit phase root.
-/

theorem qutrit_phase_root_conjugate :
    (starRingEnd ℂ) qutrit_phase_root = -1-qutrit_phase_root := by
  simp only [qutrit_phase_root, map_div₀, map_add, map_mul, map_neg,
    map_ofNat, map_one, Complex.conj_I, Complex.conj_ofReal]
  ring
