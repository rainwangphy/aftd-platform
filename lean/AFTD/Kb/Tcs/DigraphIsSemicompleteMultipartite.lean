import AFTD.Prelude

/-!
# digraph_is_semicomplete_multipartite

Topic: graphs   Node: 376e2ac4f8d9

Provenance: formalization of a published result. Source: arXiv:2610.36895 Sec. 5

A digraph D is semicomplete multipartite if it is loopless and its underlying inclusive simple graph has transitive non-adjacency (i.e., its vertex set is partitioned into independent sets with all cross-pairs having at least one directed edge).
-/

/-- A digraph is semicomplete multipartite if loopless and its underlying graph is complete multipartite. -/
def digraph_is_semicomplete_multipartite {V : Type*} (D : Digraph V) : Prop :=
  (∀ v : V, ¬ D.Adj v v) ∧ D.toSimpleGraphInclusive.IsCompleteMultipartite
