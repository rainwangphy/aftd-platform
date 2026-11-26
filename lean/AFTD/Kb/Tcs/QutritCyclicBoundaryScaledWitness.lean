import AFTD.Prelude

/-!
# qutrit_cyclic_boundary_scaled_witness

Topic: quantum   Node: fe4fc5ba4cf4

Provenance: helper lemma. OP-2299; uniform SOS identity, experiments 40308 and 40310.

A denominator-cleared cyclic boundary witness, with the output index reflected to match the convolution Choi convention.
-/

noncomputable def qutrit_cyclic_boundary_scaled_witness (t : ℝ) :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ := Matrix.of fun p q =>
    if p.1 + p.2 = 0 ∧ q.1 + q.2 = 0 then
      if p.1 = q.1 then (1 - (t : ℂ))^2 else -(1 - (t : ℂ) + (t : ℂ)^2)
    else if p = q ∧ p.1 + p.2 = 2 then (t : ℂ)^2
    else if p = q ∧ p.1 + p.2 = 1 then 1 else 0
