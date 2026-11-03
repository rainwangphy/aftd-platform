import AFTD.Prelude

/-!
# digraph_is_quasi_kernel

Topic: graphs   Node: 588a7af572a0

Provenance: helper lemma. step towards digraph_small_quasi_kernel_exists

A subset Q of vertices in a digraph D is a quasi-kernel if Q is independent (no arcs between distinct vertices of Q) and 2-dominating (every vertex v is either in Q, an out-neighbor of Q, or an out-neighbor of an out-neighbor of Q).
-/

/-- A subset Q of vertices in a digraph is a quasi-kernel if it is independent and every vertex of the digraph is in Q or reachable from Q by a directed path of length 1 or 2. -/
def digraph_is_quasi_kernel {α : Type*} (D : Digraph α) (Q : Finset α) : Prop := (∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → ¬ D.Adj u v) ∧ (∀ v, ∃ u ∈ Q, u = v ∨ D.Adj u v ∨ ∃ w, D.Adj u w ∧ D.Adj w v)
