import AFTD.Prelude
import AFTD.Kb.Tcs.QutritDiscreteBellProjector

/-!
# qutrit_bell_coefficient

Topic: quantum   Node: 732b49dd5f32

Provenance: helper lemma. OP-2299 cyclic equality-face analysis.

The real expectation of a qutrit maximally entangled basis projector.
-/

noncomputable def qutrit_bell_coefficient
    (ρ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) (u v : Fin 3) : ℝ := (∑ p : Fin 3 × Fin 3, ∑ q : Fin 3 × Fin 3,
      qutrit_discrete_bell_projector u v p q * ρ q p).re
