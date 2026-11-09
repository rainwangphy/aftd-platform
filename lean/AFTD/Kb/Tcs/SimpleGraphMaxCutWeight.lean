import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCutWeight

/-!
# simple_graph_max_cut_weight

Topic: graphs   Node: 1f5f60d30c19

Provenance: formalization of a published result. Source: arXiv:2611.05178 Section 1

Given a finite type V with decidable equality, a simple graph G on V with decidable adjacency, and an edge weighting w : G.edgeSet → ℝ, the maximum cut weight simple_graph_max_cut_weight G w is defined as the supremum over all vertex subsets S : Finset V of simple_graph_cut_weight G w S.
-/

/-- The maximum weight of a cut in an edge-weighted simple graph. -/
noncomputable def simple_graph_max_cut_weight {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : G.edgeSet → ℝ) : ℝ := ⨆ S : Finset V, simple_graph_cut_weight G w S
