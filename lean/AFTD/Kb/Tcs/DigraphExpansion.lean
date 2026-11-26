import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphOutBoundary

/-!
# digraph_expansion

Topic: graphs   Node: b5226830084a

Provenance: formalization of a published result. Source: arXiv:2611.32872 p. 3

For a finite directed graph G and a vertex subset X, the expansion b(X) is the cardinality of the out-boundary ∂^+ X.
-/

/-- The expansion b(X) = |∂⁺ X| of a vertex subset X in a digraph G. -/
def digraph_expansion {V : Type*} [Fintype V] [DecidableEq V]
    (G : Digraph V) [DecidableRel G.Adj] (X : Finset V) : ℕ := (digraph_out_boundary G X).card
