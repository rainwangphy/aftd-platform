import AFTD.Prelude
import AFTD.Kb.Tcs.GridRamseyProp

/-!
# grid_ramsey_number

Topic: combinatorics   Node: e7bc6def2a47

Provenance: formalization of a published result. Source: arXiv:2611.17378, Section 4

The `d`-dimensional grid Ramsey number `grid_ramsey_number d c` is the infimum in `ℕ` of the set of natural numbers `n` such that `grid_ramsey_prop d c n` holds.
-/

/-- The `d`-dimensional grid Ramsey number `R_d(c)` is the least integer `n` such that every `c`-coloring of `[n]^d` contains a monochromatic box. -/
noncomputable def grid_ramsey_number (d c : ℕ) : ℕ := sInf {n : ℕ | grid_ramsey_prop d c n}
