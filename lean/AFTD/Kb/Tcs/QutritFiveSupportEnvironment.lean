import AFTD.Prelude

/-!
# qutrit_five_support_environment

Topic: quantum   Node: 7a753162e515

Provenance: helper lemma. OP-2299 five-support symmetric slice, exact inverse environment 41040.

A two-parameter normalized slice, or its unnormalized cone, on the zero-Bell-coefficient face.
-/

noncomputable def qutrit_five_support_environment (l t r : ℝ) : Matrix (Fin 3) (Fin 3) ℂ := !![((3*l : ℝ) : ℂ), 0, (t : ℂ) * (1 + Complex.I * (Real.sqrt 3 : ℂ)) / 2;
      0, ((2*t : ℝ) : ℂ), 0;
      (t : ℂ) * (1 - Complex.I * (Real.sqrt 3 : ℂ)) / 2, 0, ((3*r : ℝ) : ℂ)]
