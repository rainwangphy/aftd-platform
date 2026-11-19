import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsTraceable

/-!
# SimpleGraph.IsHypotraceable

Topic: graphs   Node: c39d54161eb3

Provenance: formalization of a published result. Source: scout/2611-23018-an-infinite-family-of-bipartite-hypotraceable-graphs.md:11

A simple graph G on a vertex type V is hypotraceable if G is not traceable, but for every vertex v in V, the vertex-deleted subgraph G - v is traceable.
-/

/-- A simple graph is hypotraceable if it is not traceable but deleting any vertex yields a traceable graph. -/
def SimpleGraph.IsHypotraceable {V : Type*} [DecidableEq V] (G : SimpleGraph V) : Prop := ¬ G.IsTraceable ∧ ∀ v : V, (G.induce ({v}ᶜ : Set V)).IsTraceable
