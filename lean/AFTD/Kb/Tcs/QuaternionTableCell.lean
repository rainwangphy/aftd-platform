import AFTD.Prelude

/-!
# quaternion_table_cell

Topic: combinatorics   Node: e0d3f786fd92

Provenance: helper lemma. step towards cayley_table_graph_quaternion_chromatic_number

Quadrant coordinates for the Cayley table of QuaternionGroup N: for bits (ε, η) and i, j in ZMod (2*N), the cell in row a^i (if ε = false) or xa^i (if ε = true) and column a^j (if η = false) or xa^j (if η = true). Every cell of the table is of this form exactly once.
-/

/-- The cell of the QuaternionGroup table at row (ε, i) and column (η, j). -/
def quaternion_table_cell (N : ℕ) (ε η : Bool) (i j : ZMod (2 * N)) :
    QuaternionGroup N × QuaternionGroup N := ((if ε then QuaternionGroup.xa i else QuaternionGroup.a i),
   (if η then QuaternionGroup.xa j else QuaternionGroup.a j))
