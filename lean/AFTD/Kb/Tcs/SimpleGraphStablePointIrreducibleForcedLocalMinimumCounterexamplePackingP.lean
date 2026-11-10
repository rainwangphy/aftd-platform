import AFTD.Prelude

/-!
# simple_graph_stable_point_irreducible_forced_local_minimum_counterexample_packing_P

Topic: graphs   Node: 70b752c9d0a1

Provenance: helper lemma. step towards simple_graph_stable_point_irreducible_forced_local_minimum_counterexample

The seven-triangle packing P = {012, 567, 035, 137, 146, 236, 245}.
-/

/-- The seven-triangle packing P of the witness, containing the fully forced triangle 236. -/
def simple_graph_stable_point_irreducible_forced_local_minimum_counterexample_packing_P : Finset (Finset (Sym2 (Fin 9))) := {{s(0,1),s(0,2),s(1,2)}, {s(5,6),s(5,7),s(6,7)}, {s(0,3),s(0,5),s(3,5)},
     {s(1,3),s(1,7),s(3,7)}, {s(1,4),s(1,6),s(4,6)}, {s(2,3),s(2,6),s(3,6)},
     {s(2,4),s(2,5),s(4,5)}}
