import AFTD.Prelude

/-!
# IsFactorCritical

Topic: graphs   Node: f98d8d78a43d

Provenance: formalization of a published result. Source: arXiv:2611.09072 Section 1

A simple graph G on a vertex type V is factor-critical if for every vertex v : V, the induced subgraph of G on {v}ᶜ has a perfect matching, that is, there exists a subgraph M of G.induce ({v}ᶜ : Set V) such that M.IsPerfectMatching.
-/

/-- A simple graph is factor-critical if deleting any single vertex leaves a graph with a perfect matching. -/
def IsFactorCritical {V : Type*} (G : SimpleGraph V) : Prop := ∀ v : V, ∃ M : (G.induce ({v}ᶜ : Set V)).Subgraph, M.IsPerfectMatching
