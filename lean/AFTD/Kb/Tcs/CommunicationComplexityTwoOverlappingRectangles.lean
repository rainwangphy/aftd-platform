import AFTD.Prelude

/-!
# CommunicationComplexity.two_overlapping_rectangles

Topic: communication   Node: c3c85e944749

Provenance: formalization of a published result. Source: arXiv:2611.11488 Section 2, equation (2.1) and Section 5

The two-overlapping-rectangles Boolean function on Fin 3 × Fin 3 evaluates to false at (0, 0) and (2, 2) and to true on all other inputs.
-/

/-- The two-overlapping-rectangles Boolean function on Fin 3 × Fin 3. -/
def CommunicationComplexity.two_overlapping_rectangles (x y : Fin 3) : Bool := !((x == 0 && y == 0) || (x == 2 && y == 2))
