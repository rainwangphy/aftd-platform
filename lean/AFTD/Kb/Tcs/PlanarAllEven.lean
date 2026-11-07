import AFTD.Prelude
import AFTD.Kb.Tcs.PlanarOccupiedLines

/-!
# planar_all_even

Topic: combinatorics   Node: 73ee4192e09c

Provenance: formalization of a published result. Source: arXiv:2610.38864 Section 1 and Section 3

A finite set A in the plane is all-even if it is nonempty and for every non-zero vector u, the number of lines perpendicular to u meeting A is even.
-/

/-- A finite nonempty planar set is all-even if every direction has an even number of occupied lines. -/
def planar_all_even (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop := A.Nonempty ∧ ∀ u : EuclideanSpace ℝ (Fin 2), u ≠ 0 → Even (planar_occupied_lines A u)
