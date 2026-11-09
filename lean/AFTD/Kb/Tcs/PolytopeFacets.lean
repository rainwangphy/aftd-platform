import AFTD.Prelude
import AFTD.Kb.Tcs.IsFacet

/-!
# polytope_facets

Topic: combinatorics   Node: 6918ad0b44ae

Provenance: formalization of a published result. Source: folklore; Ziegler, Lectures on Polytopes

The set of all facets of a subset P of a real vector space is the collection of all maximal proper nonempty extreme sets of P.
-/

/-- The set of all facets of a subset P of a real vector space. -/
def polytope_facets {E : Type*} [AddCommMonoid E] [Module ℝ E] (P : Set E) : Set (Set E) := {F | is_facet P F}
