import AFTD.Prelude

/-!
# p_amp_damping

Topic: quantum   Node: 416e3e734917

Provenance: formalization of a published result. Source: arXiv:2610.37187, Section 7, Eq. (7.1)

The projection matrix P = |1⟩⟨1| onto the second standard basis state in dimension d ≥ 2.
-/

/-- The projector P = |1⟩⟨1| for amplitude damping in dimension d ≥ 2. -/
def p_amp_damping (d : ℕ) (h : 2 ≤ d) : Matrix (Fin d) (Fin d) ℂ := fun r c => if r = ⟨1, by omega⟩ ∧ c = ⟨1, by omega⟩ then 1 else 0
