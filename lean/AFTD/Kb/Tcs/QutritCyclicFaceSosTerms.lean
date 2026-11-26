import AFTD.Prelude
import AFTD.Kb.Tcs.QutritPhaseRoot

/-!
# qutrit_cyclic_face_sos_terms

Topic: quantum   Node: db98a1ca6261

Provenance: helper lemma. OP-2299 exact dual vectors 41078–41080.

Four cubic terms in an exact PPT two-copy sum-of-squares certificate on the zero-Bell face.
-/

noncomputable def qutrit_cyclic_face_sos_terms (x y : Fin 3 → ℂ) : Fin 4 → ℂ := ![
    star (x 0)*y 0*y 2 + qutrit_phase_root*star (x 1)*y 0*y 1 + qutrit_phase_root^2*star (x 2)*y 1*y 2,
    (qutrit_phase_root^2*x 0*star (y 0)*y 1 - 2*x 1*star (y 0)*y 2 + qutrit_phase_root*x 2*star (y 0)*y 0)/3 + x 2*star (y 1)*y 1,
    (qutrit_phase_root*x 0*star (y 1)*y 1 + qutrit_phase_root^2*x 1*star (y 1)*y 2 - 2*x 2*star (y 1)*y 0)/3 + x 0*star (y 2)*y 2,
    (-2*x 0*star (y 2)*y 1 + qutrit_phase_root*x 1*star (y 2)*y 2 + qutrit_phase_root^2*x 2*star (y 2)*y 0)/3 + x 1*star (y 0)*y 0]
