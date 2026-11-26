import AFTD.Prelude

/-!
# qutrit_phase_root

Topic: quantum   Node: 8074768e9f42

Provenance: helper lemma. Standard qutrit phase-space convention, e.g. https://arxiv.org/abs/quant-ph/0606083.

The primitive third root of unity used to label qutrit maximally entangled basis states.
-/

noncomputable def qutrit_phase_root : ℂ := (-1 + Complex.I * (Real.sqrt 3 : ℂ)) / 2
