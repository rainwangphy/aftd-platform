import AFTD.Prelude
import AFTD.Kb.Tcs.AffineLine

/-!
# is_cylinder_in_direction

Topic: combinatorics   Node: 51efdefab903

Provenance: formalization of a published result. Source: arXiv:2611.12153 Section 1

Let p be a prime. A subset S of (ZMod p)^3 is a cylinder in direction v if for every point P in (ZMod p)^3, the affine line through P in direction v is either contained in S or disjoint from S.
-/

/-- A set S is a cylinder in direction v if every affine line parallel to v is either contained in S or disjoint from S. -/
def is_cylinder_in_direction (p : ℕ) [Fact p.Prime] (S : Set (Fin 3 → ZMod p)) (v : Fin 3 → ZMod p) : Prop := ∀ P : Fin 3 → ZMod p, affine_line P v ⊆ S ∨ Disjoint (affine_line P v) S
