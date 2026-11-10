import AFTD.Prelude

/-!
# affine_line

Topic: combinatorics   Node: 817d1ead879a

Provenance: formalization of a published result. Source: arXiv:2611.12153 Section 2

For a natural number p, the affine line in (ZMod p)^3 through a point P in direction v is the set of points x such that x = P + t • v for some t in ZMod p.
-/

/-- The affine line through P in direction v in (ZMod p)^3. -/
def affine_line {p : ℕ} (P v : Fin 3 → ZMod p) : Set (Fin 3 → ZMod p) := {x | ∃ t : ZMod p, x = P + t • v}
