import AFTD.Prelude
import AFTD.Kb.Tcs.IsConvexFacet

/-!
# polytope_convex_facets

Topic: combinatorics   Node: 81def7283ea7

Provenance: formalization of a published result. Source: folklore; Ziegler, Lectures on Polytopes

The set of all facets of P, that is, of its maximal proper nonempty convex extreme subsets.
-/

/-- The set of facets (maximal proper nonempty convex extreme subsets) of P. -/
def polytope_convex_facets {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) : Set (Set E) := {F | is_convex_facet P F}
