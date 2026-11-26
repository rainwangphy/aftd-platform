import AFTD.Prelude
import AFTD.Kb.Tcs.QutritPhaseRoot

/-!
# qutrit_asymmetric_slice_environment

Topic: quantum   Node: 26e7545279e4

Provenance: helper lemma. OP-2299 asymmetric zero-Bell slice, exact orbit identity 40906.

The qutrit environment for Bell weights (l,l,l;u,v,0;r,r,r).
-/

noncomputable def qutrit_asymmetric_slice_environment (l u v r : ℝ) : Matrix (Fin 3) (Fin 3) ℂ := !![((3*l : ℝ) : ℂ), 0, (u : ℂ) + (v : ℂ)*qutrit_phase_root;
      0, ((u+v : ℝ) : ℂ), 0;
      (u : ℂ) + (v : ℂ)*star qutrit_phase_root, 0, ((3*r : ℝ) : ℂ)]
