import AFTD.Prelude

/-!
# simple_graph_is_fort

Topic: graphs   Node: 220899eb4194

Provenance: formalization of a published result. Source: arXiv:2611.01102 Sec. 2, Definition 2.1

For a simple graph G on an arbitrary type V, a subset F of V is a fort if F is nonempty and for every vertex v not in F, it is not the case that there exists a unique vertex u in F adjacent to v in G (¬ ∃! u, u ∈ F ∧ G.Adj v u).
-/

/-- A subset F of vertices is a fort if F is nonempty and no vertex outside F has a unique neighbor in F. -/
def simple_graph_is_fort {V : Type*} (G : SimpleGraph V) (F : Set V) : Prop := F.Nonempty ∧ ∀ v ∉ F, ¬ ∃! u, u ∈ F ∧ G.Adj v u
