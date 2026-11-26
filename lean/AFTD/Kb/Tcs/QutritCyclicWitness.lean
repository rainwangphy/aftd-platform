import AFTD.Prelude

/-!
# qutrit_cyclic_witness

Topic: quantum   Node: 76ca9cb741e3

Provenance: helper lemma. OP-2299; cyclic positive-map conditions arXiv:1403.1069 and exact uniform SOS experiments 40308 and 40310.

The three-parameter real cyclic witness in the reflected output-index convention.
-/

noncomputable def qutrit_cyclic_witness (a b c : ℝ) :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ := Matrix.of fun p q =>
    if p.1 + p.2 = 0 ∧ q.1 + q.2 = 0 then
      if p.1 = q.1 then (a : ℂ) else -1
    else if p = q ∧ p.1 + p.2 = 2 then (b : ℂ)
    else if p = q ∧ p.1 + p.2 = 1 then (c : ℂ) else 0
