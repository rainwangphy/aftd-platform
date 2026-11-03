import AFTD.Prelude

/-!
# digraph_two_dominated

Topic: graphs   Node: 66651e500ff5

Provenance: helper lemma. step towards digraph_small_quasi_kernel_exists

A vertex v is 2-dominated by a vertex set S in a digraph D if some u in S satisfies u = v, or u -> v, or u -> w -> v for some w.
-/

/-- v is 2-dominated by S: v lies in S, or is an out-neighbour of S, or is reached from S by a directed path of length two. This is exactly the second conjunct of `digraph_is_quasi_kernel`, factored out so that it can be reasoned about on its own. -/
def digraph_two_dominated {α : Type*} (D : Digraph α) (S : Finset α) (v : α) : Prop := ∃ u ∈ S, u = v ∨ D.Adj u v ∨ ∃ w, D.Adj u w ∧ D.Adj w v
