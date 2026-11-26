import AFTD.Prelude
import AFTD.Kb.Tcs.QutritPhaseRoot

/-!
# qutrit_asymmetric_face_environment

Topic: quantum   Node: ad3127945cf6

Provenance: helper lemma. OP-2299 asymmetric zero-Bell face; experiments 41045, 41048 and 41052.

A rational Bell-weight qutrit environment on the zero-coefficient face, passing the realignment numerical filter.
-/

noncomputable def qutrit_asymmetric_face_environment : Matrix (Fin 3) (Fin 3) ℂ := !![(568/1000 : ℂ), 0, (23/100 : ℂ) + (91/1000 : ℂ)*qutrit_phase_root;
      0, (321/1000 : ℂ), 0;
      (23/100 : ℂ) + (91/1000 : ℂ)*star qutrit_phase_root, 0, (111/1000 : ℂ)]
