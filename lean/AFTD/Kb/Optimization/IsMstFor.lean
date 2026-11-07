import AFTD.Prelude

/-!
# is_mst_for

Topic: submodular   Node: d4f8471eca90

Provenance: formalization of a published result. Source: scout/2610-40844-stochastic-minimum-spanning-tree-identification-with-binary.md:260

A simple graph T on a finite vertex type V is a minimum spanning tree of G under edge realization α : G.edgeSet → Bool if T is a subgraph of G (T ≤ G), T is a tree (T.IsTree), and for every other spanning tree T' of G (T' ≤ G with T'.IsTree), the number of edges e of G in T with α(e) = true is at most the number of edges e of G in T' with α(e) = true.
-/

open scoped Classical in
/-- A subgraph is an MST under realization α if it is a spanning tree of minimal weight. -/
def is_mst_for {V : Type*} [Fintype V] (G T : SimpleGraph V) (α : G.edgeSet → Bool) : Prop := T ≤ G ∧ T.IsTree ∧ ∀ T' ≤ G, T'.IsTree →
    (∑ e : G.edgeSet, if (e : Sym2 V) ∈ T.edgeSet then (if α e then 1 else 0) else 0) ≤
    (∑ e : G.edgeSet, if (e : Sym2 V) ∈ T'.edgeSet then (if α e then 1 else 0) else 0)
