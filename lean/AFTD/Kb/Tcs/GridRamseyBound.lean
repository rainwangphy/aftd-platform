import AFTD.Prelude

/-!
# grid_ramsey_bound

Topic: combinatorics   Node: 009c3d001237

Provenance: helper lemma. step towards four_grid_ramsey_two_ge_thirty_three

An explicit tower-type bound on grid Ramsey numbers: `grid_ramsey_bound 0 c = 1` and `grid_ramsey_bound (d+1) c = max (c+1) (grid_ramsey_bound d (c^(c+1)))`.
-/

/-- Explicit bound `N(d,c)` such that every `c`-colouring of `[N(d,c)]^d` contains a monochromatic box. -/
def grid_ramsey_bound : ℕ → ℕ → ℕ
| 0, _ => 1
| d + 1, c => max (c + 1) (grid_ramsey_bound d (c ^ (c + 1)))
