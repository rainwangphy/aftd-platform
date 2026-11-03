import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphWeightedCenterStrict54Graph
import AFTD.Kb.Tcs.DigraphStrict54OutMask

/-!
# digraph_strict54_adj_iff_out_mask

Topic: graphs   Node: 1c83b646422b

Provenance: helper lemma. Bitmask certificate for the 54-vertex strictness witness of the weighted center route (IN-522).

The out-mask table describes the arcs of the 54-vertex strictness witness exactly.
-/

private instance in522_strict54_adj : DecidableRel digraph_weighted_center_strict54_graph.Adj := by
  intro u v
  unfold digraph_weighted_center_strict54_graph
  infer_instance

theorem digraph_strict54_adj_iff_out_mask :
    ∀ u v : Fin 54, digraph_weighted_center_strict54_graph.Adj u v ↔ (digraph_strict54_out_mask u.val).testBit v.val = true := by
  decide +kernel
