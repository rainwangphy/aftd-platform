import AFTD.Prelude

/-!
# simple_graph_stable_forced_k4_anchor_pack

Topic: graphs   Node: b50c42f35739

Provenance: helper lemma. step towards simple_graph_stable_forced_k4_anchor_unforced_counterexample

The eight packed triangles of the counterexample: {0,4,5}, {3,6,7}, {0,6,8}, {3,4,8}, {1,4,6}, {2,4,7}, {2,5,6}, {5,7,8}.
-/

/-- The full-support maximum triangle packing P of the witness graph. -/
def simple_graph_stable_forced_k4_anchor_pack : Finset (Finset (Fin 9)) := {{0,4,5},{3,6,7},{0,6,8},{3,4,8},{1,4,6},{2,4,7},{2,5,6},{5,7,8}}
