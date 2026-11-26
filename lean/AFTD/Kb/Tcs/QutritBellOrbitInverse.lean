import AFTD.Prelude

/-!
# qutrit_bell_orbit_inverse

Topic: quantum   Node: bf8951aa8fe1

Provenance: helper lemma. OP-2299; qutrit convolution, experiments 40125-40126 and 40163-40166.

Explicit matrix operation for the two-qutrit shift-orbit reduction.
-/

noncomputable def qutrit_bell_orbit_inverse (ρ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ := Matrix.of fun i j => 3 * ρ (i,-j) (j,-i)
