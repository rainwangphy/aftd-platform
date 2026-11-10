import AFTD.Prelude

/-!
# simple_graph_stable_point_irreducible_forced_local_minimum_counterexample_triangles

Topic: graphs   Node: 9080bd0b9a4f

Provenance: helper lemma. step towards simple_graph_stable_point_irreducible_forced_local_minimum_counterexample

The 35 three-edge sets of triangles of the witness graph, written explicitly.
-/

/-- The 35 triangle edge-sets of the witness graph, explicitly listed. -/
def simple_graph_stable_point_irreducible_forced_local_minimum_counterexample_triangles : Finset (Finset (Sym2 (Fin 9))) := {{s(0,1),s(0,2),s(1,2)}, {s(0,1),s(0,3),s(1,3)}, {s(0,1),s(0,5),s(1,5)},
     {s(0,2),s(0,3),s(2,3)}, {s(0,2),s(0,5),s(2,5)}, {s(0,3),s(0,5),s(3,5)},
     {s(1,2),s(1,3),s(2,3)}, {s(1,2),s(1,4),s(2,4)}, {s(1,2),s(1,5),s(2,5)},
     {s(1,2),s(1,6),s(2,6)}, {s(1,3),s(1,4),s(3,4)}, {s(1,3),s(1,5),s(3,5)},
     {s(1,3),s(1,6),s(3,6)}, {s(1,3),s(1,7),s(3,7)}, {s(1,4),s(1,5),s(4,5)},
     {s(1,4),s(1,6),s(4,6)}, {s(1,5),s(1,6),s(5,6)}, {s(1,5),s(1,7),s(5,7)},
     {s(1,6),s(1,7),s(6,7)}, {s(2,3),s(2,4),s(3,4)}, {s(2,3),s(2,5),s(3,5)},
     {s(2,3),s(2,6),s(3,6)}, {s(2,3),s(2,8),s(3,8)}, {s(2,4),s(2,5),s(4,5)},
     {s(2,4),s(2,6),s(4,6)}, {s(2,5),s(2,6),s(5,6)}, {s(2,6),s(2,8),s(6,8)},
     {s(3,4),s(3,5),s(4,5)}, {s(3,4),s(3,6),s(4,6)}, {s(3,5),s(3,6),s(5,6)},
     {s(3,5),s(3,7),s(5,7)}, {s(3,6),s(3,7),s(6,7)}, {s(3,6),s(3,8),s(6,8)},
     {s(4,5),s(4,6),s(5,6)}, {s(5,6),s(5,7),s(6,7)}}
