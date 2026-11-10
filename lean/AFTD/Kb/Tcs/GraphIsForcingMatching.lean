import AFTD.Prelude

/-!
# graph_is_forcing_matching

Topic: graphs   Node: a7f56f0fbd96

Provenance: formalization of a published result. Source: arXiv:2611.11813 Section 1

A subgraph S of a simple graph G is a forcing matching if S is a matching and there is a unique perfect matching M of G with S ≤ M.
-/

/-- A subgraph S of G is a forcing matching if S is a matching contained in a unique perfect matching of G. -/
def graph_is_forcing_matching {V : Type*} (G : SimpleGraph V) (S : G.Subgraph) : Prop := S.IsMatching ∧ ∃! M : G.Subgraph, M.IsPerfectMatching ∧ S ≤ M
