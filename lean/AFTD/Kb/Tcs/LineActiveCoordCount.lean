import AFTD.Prelude

/-!
# line_active_coord_count

Topic: combinatorics   Node: e13571dcd6c1

Provenance: formalization of a published result. Source: arXiv:2611.22205 Section 2

For a combinatorial line l of type Combinatorics.Line α ι over an arbitrary finite type ι, line_active_coord_count l is the number of active coordinates, defined as the number of indices i : ι such that (l.idxFun i).isNone is true.
-/

/-- The number of active coordinates of a combinatorial line. -/
def line_active_coord_count {α ι : Type*} [Fintype ι] (l : Combinatorics.Line α ι) : ℕ := (Finset.univ.filter fun i => (l.idxFun i).isNone).card
