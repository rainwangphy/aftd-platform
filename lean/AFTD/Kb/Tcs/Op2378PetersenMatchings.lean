import AFTD.Prelude
import AFTD.Kb.Tcs.Op2378PetersenEdges

/-!
# op_2378_petersen_matchings

Topic: graphs   Node: e365407dee72

Provenance: helper lemma. step towards op_2378_partial_r_two

The list of the six perfect matchings of the Petersen graph: the five spokes, and the five matchings each consisting of two outer edges, two inner edges and one spoke.
-/

/-- The six perfect matchings of the Petersen graph, listed explicitly. -/
def op_2378_petersen_matchings : Finset (Finset (Sym2 (Fin 10))) := {{s(0,5), s(1,6), s(2,7), s(3,8), s(4,9)},
     {s(0,1), s(2,3), s(4,9), s(5,7), s(6,8)},
     {s(0,4), s(1,2), s(3,8), s(5,7), s(6,9)},
     {s(0,1), s(2,7), s(3,4), s(5,8), s(6,9)},
     {s(0,4), s(1,6), s(2,3), s(5,8), s(7,9)},
     {s(0,5), s(1,2), s(3,4), s(6,8), s(7,9)}}
