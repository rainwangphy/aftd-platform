import AFTD.Prelude

/-!
# qutrit_bell_orbit_slice

Topic: quantum   Node: ebf3ee906e8e

Provenance: helper lemma. OP-2299; qutrit convolution, experiments 40125-40126 and 40163-40166.

Explicit matrix operation for the two-qutrit shift-orbit reduction.
-/

def qutrit_bell_orbit_slice (ρ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) : Prop := (∀ a b c d : Fin 3, b-a ≠ d-c → ρ (a,b) (c,d)=0) ∧
  (∀ a b c d : Fin 3, ρ (a+1,b+1) (c+1,d+1)=ρ (a,b) (c,d))
