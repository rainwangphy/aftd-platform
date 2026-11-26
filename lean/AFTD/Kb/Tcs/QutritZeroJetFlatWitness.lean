import AFTD.Prelude

/-!
# qutrit_zero_jet_flat_witness

Topic: quantum   Node: cff032f4f635

Provenance: helper lemma. OP-2299; coordinate-zero local jet, experiments 40338, 40339, and 40344.

A Hermitian invariant witness with zero distinguished diagonal and remaining real diagonal coefficients b,c.
-/

noncomputable def qutrit_zero_jet_flat_witness (b c : ℝ) (u v q : ℂ) : Matrix (Fin 9) (Fin 9) ℂ := !![0, 0, 0, 0, 0, u, 0, v, 0;
    0, (b : ℂ), 0, q, 0, 0, 0, 0, star u;
    0, 0, (c : ℂ), 0, star v, 0, star q, 0, 0;
    0, star q, 0, (c : ℂ), 0, 0, 0, 0, star v;
    0, 0, v, 0, 0, 0, u, 0, 0;
    star u, 0, 0, 0, 0, (b : ℂ), 0, q, 0;
    0, 0, q, 0, star u, 0, (b : ℂ), 0, 0;
    star v, 0, 0, 0, 0, star q, 0, (c : ℂ), 0;
    0, u, 0, v, 0, 0, 0, 0, 0]
