import AFTD.Prelude

/-!
# qutrit_mub_witness_flat

Topic: quantum   Node: 8327b73b1df0

Provenance: helper lemma. OP-2299; partial transpose of the explicit optimal witness from https://arxiv.org/abs/2503.04158, Eq. 14; exact SOS experiments 40358 and 40360.

The partial transpose of a published optimal Bell-diagonal two-qutrit witness, in the convolution orbit convention.
-/

noncomputable def qutrit_mub_witness_flat : Matrix (Fin 9) (Fin 9) ℂ := !![0, 0, 0, 0, 0, -2, 0, -2, 0;
    0, 3, 0, 1, 0, 0, 0, 0, -2;
    0, 0, 3, 0, -2, 0, 1, 0, 0;
    0, 1, 0, 3, 0, 0, 0, 0, -2;
    0, 0, -2, 0, 0, 0, -2, 0, 0;
    -2, 0, 0, 0, 0, 3, 0, 1, 0;
    0, 0, 1, 0, -2, 0, 3, 0, 0;
    -2, 0, 0, 0, 0, 1, 0, 3, 0;
    0, -2, 0, -2, 0, 0, 0, 0, 0]
