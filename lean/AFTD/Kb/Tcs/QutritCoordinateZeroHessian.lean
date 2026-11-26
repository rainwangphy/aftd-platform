import AFTD.Prelude

/-!
# qutrit_coordinate_zero_hessian

Topic: quantum   Node: 21a865982416

Provenance: helper lemma. OP-2299 exact jet computation 41027.

The complex 4 by 4 matrix whose realification gives the local quadratic jet at |0,0>.
-/

noncomputable def qutrit_coordinate_zero_hessian
    (a b : ℝ) (t u v : ℂ) : Matrix (Fin 4) (Fin 4) ℂ := !![(b : ℂ), star t, 0, star v;
      t, (a : ℂ), u, 0;
      0, star u, (a : ℂ), star t;
      v, 0, t, (b : ℂ)]
