import AFTD.Prelude

/-!
# v_amp_damping

Topic: quantum   Node: 69d93ff4a0db

Provenance: formalization of a published result. Source: arXiv:2610.37187, Section 7, Eq. (7.1)

The matrix unit V = |0⟩⟨1| in the standard basis of d × d complex matrices for d ≥ 2.
-/

/-- The transition matrix V = |0⟩⟨1| for amplitude damping in dimension d ≥ 2. -/
def v_amp_damping (d : ℕ) (h : 2 ≤ d) : Matrix (Fin d) (Fin d) ℂ := fun r c => if r = ⟨0, by omega⟩ ∧ c = ⟨1, by omega⟩ then 1 else 0
