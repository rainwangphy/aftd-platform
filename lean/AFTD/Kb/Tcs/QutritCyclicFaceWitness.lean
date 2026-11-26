import AFTD.Prelude
import AFTD.Kb.Tcs.QutritDiscreteBellProjector

/-!
# qutrit_cyclic_face_witness

Topic: quantum   Node: 70c38c4136e6

Provenance: helper lemma. OP-2299 cyclic zero-face witness and exact PPT-two-copy dual identity 41079.

The cyclic product inequality witness on the face where the (1,2) Bell coefficient is zero.
-/

noncomputable def qutrit_cyclic_face_witness : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ := -qutrit_discrete_bell_projector 1 0 + qutrit_discrete_bell_projector 1 1 +
    qutrit_discrete_bell_projector 2 0 + qutrit_discrete_bell_projector 2 1 + qutrit_discrete_bell_projector 2 2
