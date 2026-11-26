import AFTD.Prelude

/-!
# qutrit_bob_transpose

Topic: quantum   Node: 74f3768005f3

Provenance: helper lemma. OP-2299; qutrit convolution, experiments 40125-40126 and 40163-40166.

Explicit matrix operation for the two-qutrit shift-orbit reduction.
-/

noncomputable def qutrit_bob_transpose (ρ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ := Matrix.of fun p q => ρ (p.1,q.2) (q.1,p.2)
