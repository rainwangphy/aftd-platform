import AFTD.Prelude

/-!
# quaternion_table_symbol

Topic: combinatorics   Node: 73f67cd94564

Provenance: helper lemma. step towards cayley_table_graph_quaternion_chromatic_number

The product symbol of a quadrant cell, written in the block coordinates of QuaternionGroup N: the bit ε ≠ η records whether the product lies in the coset xA (i.e. is of the form xa ...), and the ZMod (2*N) component is the corresponding index (i + j for AA, j - i for A/xA, i + j for xA/A, N + j - i for xA/xA).
-/

/-- The product of the cell at quadrant coordinates (ε, i), (η, j), as a coset bit and an index. -/
def quaternion_table_symbol (N : ℕ) (ε η : Bool) (i j : ZMod (2 * N)) : Bool × ZMod (2 * N) := (ε != η, match ε, η with
    | false, false => i + j
    | false, true => j - i
    | true, false => i + j
    | true, true => ((N : ℕ) : ZMod (2 * N)) + j - i)
