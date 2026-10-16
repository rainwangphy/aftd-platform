import AFTD.Prelude

/-!
# digraph_edge_count

Topic: graphs   Node: 7b51c5a5aa96

Provenance: formalization of a published result. Source: arXiv:2610.21381 (Optimally large cuts in both directions), Sec. 1 (m = |E(G)|; digraphs have no loops and at most one edge per ordered pair).

The number m of edges (arcs) of a finite digraph G.
-/

/-- The number of arcs of a finite digraph (ordered pairs `(u, v)` with `G.Adj u v`). -/
def digraph_edge_count {V : Type*} [Fintype V] (G : Digraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.filter fun p : V × V => G.Adj p.1 p.2).card
