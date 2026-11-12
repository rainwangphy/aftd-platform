import AFTD.Prelude
import AFTD.Kb.NumberTheory.EisensteinOmega

/-!
# triangular_lattice

Topic: combinatorics   Node: d13299b58489

Provenance: formalization of a published result. Source: arXiv:2611.13535, Section 2

The triangular lattice with spacing d in the complex plane is the set of points of the form d * (a + b * eisensteinOmega) for integers a and b, where eisensteinOmega is the primitive cube root of unity (-1 + i * √3)/2.
-/

/-- The triangular lattice in the complex plane with spacing parameter d. -/
def triangular_lattice (d : ℝ) : Set ℂ := {z : ℂ | ∃ a b : ℤ, z = (d : ℂ) * ((a : ℂ) + (b : ℂ) * eisensteinOmega)}
