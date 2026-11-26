import AFTD.Prelude
import AFTD.Kb.Tcs.QutritPhaseRoot

/-!
# qutrit_discrete_bell_projector

Topic: quantum   Node: 611066ad8966

Provenance: helper lemma. Standard qutrit orbit convention, e.g. https://arxiv.org/abs/quant-ph/0606083.

The normalized qutrit maximally entangled projector indexed by shift u and phase v.
-/

noncomputable def qutrit_discrete_bell_projector (u v : Fin 3) :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ := Matrix.of fun p q =>
    if p.2 = p.1+u ∧ q.2 = q.1+u then
      qutrit_phase_root^(v.val*p.1.val) * star (qutrit_phase_root^(v.val*q.1.val)) / 3
    else 0
