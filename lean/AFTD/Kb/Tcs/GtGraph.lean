import AFTD.Prelude
import AFTD.Kb.Tcs.GtAdj
import AFTD.Kb.Tcs.GtVertex

/-!
# gt_graph

Topic: graphs   Node: 9e51dd744c5f

Provenance: formalization of a published result. Source: arXiv:2611.11352 Definition 2

The simple graph gt_graph t on vertex type GtVertex t, defined as SimpleGraph.fromRel (gt_adj t).
-/

/-- The simple graph G_t. -/
def gt_graph (t : ℕ) : SimpleGraph (GtVertex t) := SimpleGraph.fromRel (gt_adj t)
