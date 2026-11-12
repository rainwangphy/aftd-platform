import AFTD.Prelude

/-!
# simple_graph_vertex_dominated

Topic: graphs   Node: 4a4df7218fa6

Provenance: formalization of a published result. Source: arXiv:2611.14430 Section 2

A vertex $v$ of a simple graph $H$ is dominated if there exists a vertex $t \neq v$ in $H$ such that the closed neighbourhood of $v$ is contained in the closed neighbourhood of $t$, that is, $N_H[v] \subseteq N_H[t]$.
-/

/-- A vertex v is dominated by another vertex in H if its closed neighbourhood is contained in that of the other vertex. -/
def simple_graph_vertex_dominated {V : Type*} (H : SimpleGraph V) (v : V) : Prop := ∃ t : V, t ≠ v ∧ insert v (H.neighborSet v) ⊆ insert t (H.neighborSet t)
