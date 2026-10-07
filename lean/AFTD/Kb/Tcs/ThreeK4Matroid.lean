import AFTD.Prelude
import AFTD.Kb.Tcs.K4CycleMatroid

/-!
# three_k4_matroid

Topic: combinatorics   Node: ac322eef75d9

Provenance: formalization of a published result. Source: arXiv:2610.07318 (A note on the list chromatic number of two matroids), proof of Theorem 1.1 (M₁)

The cycle matroid M₁ of three disjoint copies of K₄, on the ground set {0,1,2} × {edges of K₄}.
-/

/-- The cycle matroid of three disjoint copies of `K₄`. -/
def three_k4_matroid : Matroid (Fin 3 × Fin 6) := Matroid.sum' fun _ => k4_cycle_matroid
