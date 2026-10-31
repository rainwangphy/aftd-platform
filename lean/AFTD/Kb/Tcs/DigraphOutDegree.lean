import AFTD.Prelude

/-!
# digraph_out_degree

Topic: graphs   Node: ee5277a6f036

Provenance: formalization of a published result. Source: arXiv:2610.39702, Section 2.1

The out-degree d⁺(v) of a vertex v in a finite directed graph D is the number of out-neighbors of v, that is, the cardinality of the set of vertices w such that there is an arc from v to w.
-/

/-- The out-degree of a vertex in a finite directed graph. -/
def digraph_out_degree {V : Type*} [Fintype V] (D : Digraph V) [DecidableRel D.Adj] (v : V) : ℕ := (Finset.univ.filter (D.Adj v)).card
