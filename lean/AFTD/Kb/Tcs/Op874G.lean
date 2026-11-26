import AFTD.Prelude
import AFTD.Kb.Tcs.Op874E
import AFTD.Kb.Tcs.Op874V

/-!
# op874G

Topic: graphs   Node: e63bb06f964c

Provenance: helper lemma. step towards op874_mixed_matching_overlap_gadget_chain

The gadget chain graph, built from the edge set.
-/

/-- The gadget chain graph, as the simple graph on its edge set. -/
def op874G (k : ℕ) [NeZero k] : SimpleGraph (op874V k) := SimpleGraph.fromEdgeSet (op874E k)
