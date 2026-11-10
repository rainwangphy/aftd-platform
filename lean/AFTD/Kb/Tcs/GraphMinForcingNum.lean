import AFTD.Prelude
import AFTD.Kb.Tcs.GraphIsForcingMatching

/-!
# graph_min_forcing_num

Topic: graphs   Node: 252878d61992

Provenance: formalization of a published result. Source: arXiv:2611.11813 Section 1

The minimum forcing number graph_min_forcing_num G of a simple graph G is the infimum in ℕ∞ of the extended cardinalities S.edgeSet.encard over all subgraphs S of G that are forcing matchings of G.
-/

/-- The minimum forcing number f(G) of a simple graph G is the infimum in ℕ∞ of the sizes of forcing matchings. -/
noncomputable def graph_min_forcing_num {V : Type*} (G : SimpleGraph V) : ℕ∞ := ⨅ (S : G.Subgraph) (_ : graph_is_forcing_matching G S), S.edgeSet.encard
