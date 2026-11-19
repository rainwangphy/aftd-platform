import AFTD.Prelude
import AFTD.Kb.Tcs.ParityGameEncode

/-!
# parity_game_encode_two_vertex_example

Topic: automata   Node: d6a797405b59

Provenance: helper lemma. Sanity lemma for the encoding used to state OP-37

The encoding of the two-vertex game with owners (Even, Odd), priorities (0, 1), edges 0→1 and 1→0, and start vertex 1 is the 14-bit list 110 10 1 0 01 0 10 10 (1 = true): n = 2 in unary, the vertex 1 in unary, then the blocks of vertices 0 and 1.
-/

theorem parity_game_encode_two_vertex_example :
    parity_game_encode 2 ![true, false] ![0, 1] (fun u w => decide (u ≠ w)) 1 =
      [true, true, false, true, false, true, false, false, true, false, true, false, true, false] := by
  decide
