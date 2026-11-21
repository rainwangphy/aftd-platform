import AFTD.Prelude
import AFTD.Kb.Tcs.BoundarySevenBlockExampleCrossEdgeEssential

/-!
# boundary_seven_block_example_min_degree

Topic: graphs   Node: d21c9dff19e2

Provenance: helper lemma. OP-1957: explicit odd-shore obstruction.

Every vertex of the explicitly defined 28-vertex example has degree at least sixteen.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem boundary_seven_block_example_min_degree :
    ∀ v, 16 ≤ (in1122_boundary_graph28.neighborFinset v).card := by
  decide
