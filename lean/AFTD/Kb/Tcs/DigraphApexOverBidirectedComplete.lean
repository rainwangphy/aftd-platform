import AFTD.Prelude

/-!
# digraph_apex_over_bidirected_complete

Topic: graphs   Node: 6ea80a64f918

Provenance: original. Related work: arXiv:2610.21381 (Optimally large cuts in both directions), Sec. 6 (the paper's example for d = 2: a bidirected triangle and a vertex sending edges to its three vertices); here for every d.

The digraph D_d on d + 2 vertices: a bidirected complete graph on the vertices 0, …, d, together with an apex d + 1 that sends an arc to every other vertex and receives none. It has no loops, minimum outdegree d and (d + 1)² arcs.
-/

/-- Bidirected `K_{d+1}` on `0, …, d` plus an apex `d + 1` with arcs to all of them (no arcs into the apex). -/
def digraph_apex_over_bidirected_complete (d : ℕ) : Digraph (Fin (d + 2)) :=
  { Adj := fun u v => u ≠ v ∧ v ≠ Fin.last (d + 1) }
