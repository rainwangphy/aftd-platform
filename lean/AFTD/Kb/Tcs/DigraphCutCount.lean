import AFTD.Prelude

/-!
# digraph_cut_count

Topic: graphs   Node: 6c8b5a5b0717

Provenance: formalization of a published result. Source: arXiv:2610.21381 (Optimally large cuts in both directions), Sec. 1 (notation e_G(A, B)).

e_G(A, B): the number of edges of the digraph G from a vertex of A to a vertex of B.
-/

/-- `e_G(A, B)`: the number of arcs `u → v` of `G` with `u ∈ A` and `v ∈ B`. -/
def digraph_cut_count {V : Type*} [Fintype V] (G : Digraph V) [DecidableRel G.Adj]
    (A B : Finset V) : ℕ :=
  ((A ×ˢ B).filter fun p => G.Adj p.1 p.2).card
