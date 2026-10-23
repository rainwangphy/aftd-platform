import AFTD.Prelude

/-!
# young_diagram_part_gcd

Topic: combinatorics   Node: 897f06cb63ec

Provenance: formalization of a published result. Source: arXiv:2610.29291 Theorem 3.4

The greatest common divisor of the row lengths of a Young diagram $\lambda$.
-/

/-- The greatest common divisor of the row lengths of a Young diagram. -/
def young_diagram_part_gcd (μ : YoungDiagram) : ℕ := μ.rowLens.foldr Nat.gcd 0
