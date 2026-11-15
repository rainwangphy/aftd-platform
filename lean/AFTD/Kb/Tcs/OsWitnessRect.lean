import AFTD.Prelude
import AFTD.Kb.Tcs.OsWitnessRectG

/-!
# os_witness_rect

Topic: combinatorics   Node: 9a42b8b9e1d7

Provenance: helper lemma. step towards oriented_star_ge_two_edges_not_os

The digraphon W(x, y) = g(y) whose column is a rectangle sharing a full side with the square, with g the indicator of (0, 1/4).
-/

/-- The pure-case witness digraphon: 1 for y in (0,1/4) and 0 elsewhere; W^+ is constant 1/4 and W^- = g, which refutes OS when the centre has in-degree 0. -/
noncomputable def os_witness_rect : ℝ → ℝ → ℝ := fun _ y => os_witness_rect_g y
