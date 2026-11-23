import AFTD.Prelude

/-!
# is_graph_core

Topic: graphs   Node: 12e35f67f244

Provenance: formalization of a published result. Source: arXiv:2611.18633 Definition 1.1

In a locally finite simple graph G, a nonempty finset of vertices S is a core if every vertex in S has at least as many neighbors in S as in V \ S.
-/

/-- A core of a locally finite simple graph is a nonempty finset in which every member has at least as many neighbors inside as outside. -/
def is_graph_core {V : Type*} [DecidableEq V] (G : SimpleGraph V) [∀ v : V, Fintype (G.neighborSet v)] (S : Finset V) : Prop := S.Nonempty ∧ ∀ v ∈ S, (G.neighborFinset v \ S).card ≤ (G.neighborFinset v ∩ S).card
