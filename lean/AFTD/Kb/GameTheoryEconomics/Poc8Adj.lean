import AFTD.Prelude

/-!
# poc8_adj

Topic: fair_division   Node: be220e6d7300

Adjacency of the 8-vertex graph with the 18 edges 04, 05, 06, 07, 13, 15, 16, 17, 23, 24, 26, 27, 36, 37, 45, 47, 57, 67, stored as neighbourhood bitmasks.
-/

/-- Adjacency of the 8-vertex counterexample graph (18 edges), as neighbourhood bitmasks. -/
def poc8_adj (a b : Fin 8) : Bool :=
  ((![240, 232, 216, 198, 165, 147, 143, 127] : Fin 8 → ℕ) a).testBit b
