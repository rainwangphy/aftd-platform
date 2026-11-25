import AFTD.Prelude

/-!
# is_even_factor

Topic: graphs   Node: c974d21bb1e7

Provenance: formalization of a published result. Source: arXiv:2611.32276, Section 1

An even factor of a finite simple graph $G$ is a spanning subgraph $H$ of $G$ such that every vertex has even degree in $H$.
-/

/-- An even factor of a simple graph is a spanning subgraph in which every vertex degree is even. -/
def is_even_factor {V : Type*} [Fintype V] (G : SimpleGraph V) (H : SimpleGraph V) : Prop := H ≤ G ∧ ∀ v : V, Even (Nat.card (H.neighborSet v))
