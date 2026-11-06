import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphOutDegree

/-!
# digraph_exceptional_verts

Topic: graphs   Node: b122db91bd2c

Provenance: formalization of a published result. Source: arXiv:2611.00720, Section 1

For a finite directed graph D on a finite vertex type V with decidable adjacency, the set of exceptional vertices O(D) is the finite set of vertices in V whose out-degree in D is equal to 1.
-/

/-- The set of exceptional vertices of a finite directed graph D, which are those vertices with out-degree exactly one. -/
def digraph_exceptional_verts {V : Type*} [Fintype V] (D : Digraph V) [DecidableRel D.Adj] : Finset V := Finset.univ.filter (fun v => digraph_out_degree D v = 1)
