import AFTD.Prelude

/-!
# is_unicyclic

Topic: graphs   Node: 1a95c8cd35a7

Provenance: formalization of a published result. Source: Harary, Graph Theory (1969), Chapter 4

A simple graph G on a finite vertex set V is unicyclic if G is connected and its number of edges equals its number of vertices.
-/

/-- A finite simple graph is unicyclic if it is connected and its number of edges equals its number of vertices. -/
def is_unicyclic {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop := open scoped Classical in G.Connected ∧ G.edgeFinset.card = Fintype.card V
