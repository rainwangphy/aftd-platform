import AFTD.Prelude
import AFTD.Kb.Tcs.FiveVertexTStar

/-!
# five_vertex_t_star_adj_decidable

Topic: graphs   Node: 590bdfec7dbc

Provenance: helper lemma. step towards lly_positive_edge_connectivity_threshold_five

Adjacency in the T-graph is decidable.
-/

/-- Makes `five_vertex_t_star.Adj` decidable, so `decide` can settle adjacency, degrees and connectivity for it. Necessary because the `DecidableRel` instance of a *named* graph does not synthesise by unfolding. -/
instance five_vertex_t_star_adj_decidable : DecidableRel five_vertex_t_star.Adj := by unfold five_vertex_t_star; infer_instance
