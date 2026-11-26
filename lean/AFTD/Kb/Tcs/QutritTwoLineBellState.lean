import AFTD.Prelude
import AFTD.Kb.Tcs.QutritDiscreteBellProjector

/-!
# qutrit_two_line_bell_state

Topic: quantum   Node: c31582e24c8b

Provenance: helper lemma. OP-2299 two-line support analysis.

A Bell-diagonal matrix supported on the union of the two intersecting coordinate lines.
-/

noncomputable def qutrit_two_line_bell_state (a b c d e : ℝ) : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ := Matrix.of fun p q =>
      (a : ℂ) * qutrit_discrete_bell_projector 0 0 p q +
      (b : ℂ) * qutrit_discrete_bell_projector 0 1 p q +
      (c : ℂ) * qutrit_discrete_bell_projector 0 2 p q +
      (d : ℂ) * qutrit_discrete_bell_projector 1 0 p q +
      (e : ℂ) * qutrit_discrete_bell_projector 2 0 p q
