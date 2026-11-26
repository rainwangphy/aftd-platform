import AFTD.Prelude

/-!
# digraph_closed_out_nbr

Topic: graphs   Node: 1dcf662ce2b5

Provenance: formalization of a published result. Source: arXiv:2611.32872 p. 3

For a finite directed graph G and a vertex subset X, the closed out-neighborhood N_G^+[X] is the union of X and all vertices y such that some vertex in X has an edge to y.
-/

/-- The closed out-neighborhood N_G⁺[X] of a vertex subset X in a digraph G. -/
def digraph_closed_out_nbr {V : Type*} [Fintype V] [DecidableEq V]
    (G : Digraph V) [DecidableRel G.Adj] (X : Finset V) : Finset V := X ∪ (Finset.univ.filter fun y => ∃ x ∈ X, G.Adj x y)
