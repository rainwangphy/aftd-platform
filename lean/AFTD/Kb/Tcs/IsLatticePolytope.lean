import AFTD.Prelude

/-!
# is_lattice_polytope

Topic: combinatorics   Node: 48a18b7d5b96

Provenance: formalization of a published result. Source: arXiv:2611.08819 Section 1; Batyrev 1994

A subset P of ℝ^d is a lattice polytope if P is the convex hull of the real embeddings of a finite set of integer lattice vectors in ℤ^d.
-/

/-- A subset of ℝ^d is a lattice polytope if it is the convex hull of a finite set of integer lattice points. -/
def is_lattice_polytope {d : ℕ} (P : Set (Fin d → ℝ)) : Prop := ∃ S : Finset (Fin d → ℤ), P = convexHull ℝ ((fun z i => (z i : ℝ)) '' (S : Set (Fin d → ℤ)))
