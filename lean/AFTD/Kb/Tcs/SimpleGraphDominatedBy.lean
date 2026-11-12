import AFTD.Prelude

/-!
# simple_graph_dominated_by

Topic: graphs   Node: 4f71abb4a5af

Provenance: formalization of a published result. Source: arXiv:2611.14430, Section 2

A vertex $u$ is dominated by a distinct vertex $t$ in a simple graph $G$ if the closed neighborhood of $u$ is contained in the closed neighborhood of $t$.
-/

/-- A vertex u is dominated by distinct vertex t if the closed neighborhood of u is a subset of that of t. -/
def simple_graph_dominated_by {V : Type*} (G : SimpleGraph V) (u t : V) : Prop :=
  u ≠ t ∧ insert u (G.neighborSet u) ⊆ insert t (G.neighborSet t)
