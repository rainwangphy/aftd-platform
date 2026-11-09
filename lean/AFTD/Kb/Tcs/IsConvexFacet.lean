import AFTD.Prelude

/-!
# is_convex_facet

Topic: combinatorics   Node: 2311e41579d0

Provenance: formalization of a published result. Source: folklore; Ziegler, Lectures on Polytopes (faces of a polytope are its convex extreme subsets)

F is a facet of P if F is a maximal proper nonempty convex extreme subset of P: among the convex extreme subsets of P, no one other than F and P contains F. For a polytope these are exactly the facets in the usual sense.
-/

/-- A facet of P: a maximal proper nonempty convex extreme subset of P. -/
def is_convex_facet {E : Type*} [AddCommGroup E] [Module ℝ E] (P F : Set E) : Prop := IsExtreme ℝ P F ∧ Convex ℝ F ∧ F.Nonempty ∧ F ≠ P ∧ ∀ G, IsExtreme ℝ P G → Convex ℝ G → F ⊆ G → G = F ∨ G = P
