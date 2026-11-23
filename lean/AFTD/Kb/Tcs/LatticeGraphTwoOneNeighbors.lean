import AFTD.Prelude
import AFTD.Kb.Tcs.LatticeBallOne

/-!
# lattice_graph_two_one_neighbors

Topic: graphs   Node: c1fa2287e613

Provenance: formalization of a published result. Source: arXiv:2611.18633 Section 1

For v : ℤ × ℤ, lattice_graph_two_one_neighbors v is the Finset (ℤ × ℤ) defined by erasing v from lattice_ball_one v.
-/

/-- The finset of 8 neighbors of v in the radius-one lattice graph G_{2,1}. -/
def lattice_graph_two_one_neighbors (v : ℤ × ℤ) : Finset (ℤ × ℤ) := (lattice_ball_one v).erase v
