import AFTD.Prelude

/-!
# simple_graph_stable_point_irreducible_forced_local_minimum_counterexample_packing_Q

Topic: graphs   Node: dcf6ab0f0c06

Provenance: helper lemma. step towards simple_graph_stable_point_irreducible_forced_local_minimum_counterexample

The seven-triangle packing Q = {368, 013, 567, 025, 126, 145, 234}, with no fully forced triangle.
-/

/-- The seven-triangle packing Q of the witness, in which no triangle is fully forced. -/
def simple_graph_stable_point_irreducible_forced_local_minimum_counterexample_packing_Q : Finset (Finset (Sym2 (Fin 9))) := {{s(3,6),s(3,8),s(6,8)}, {s(0,1),s(0,3),s(1,3)}, {s(5,6),s(5,7),s(6,7)},
     {s(0,2),s(0,5),s(2,5)}, {s(1,2),s(1,6),s(2,6)}, {s(1,4),s(1,5),s(4,5)},
     {s(2,3),s(2,4),s(3,4)}}
