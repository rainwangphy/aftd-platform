import AFTD.Prelude

/-!
# op_2378_petersen_edges

Topic: graphs   Node: 18c988825e37

Provenance: helper lemma. step towards op_2378_partial_r_two

The 15-edge list of the Petersen graph on Fin 10: outer 5-cycle 0-1-2-3-4, inner 5-cycle 5-7-9-6-8, spokes 05,16,27,38,49.
-/

/-- The 15 edges of the Petersen graph, as a Finset of unordered pairs on Fin 10. -/
def op_2378_petersen_edges : Finset (Sym2 (Fin 10)) := {s(0,1), s(0,4), s(0,5), s(1,2), s(1,6), s(2,3), s(2,7), s(3,4), s(3,8),
     s(4,9), s(5,7), s(5,8), s(6,8), s(6,9), s(7,9)}
