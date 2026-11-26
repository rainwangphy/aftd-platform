import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphClosedOutNbr

/-!
# digraph_out_boundary

Topic: graphs   Node: d61d51e6f240

Provenance: formalization of a published result. Source: arXiv:2611.32872 p. 3

For a finite directed graph G and a vertex subset X, the out-boundary ∂^+ X is the set difference between the closed out-neighborhood N_G^+[X] and X.
-/

/-- The out-boundary ∂⁺ X = N_G⁺[X] \ X of a vertex subset X in a digraph G. -/
def digraph_out_boundary {V : Type*} [Fintype V] [DecidableEq V]
    (G : Digraph V) [DecidableRel G.Adj] (X : Finset V) : Finset V := digraph_closed_out_nbr G X \ X
