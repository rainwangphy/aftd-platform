import AFTD.Prelude

/-!
# grid_graph

Topic: combinatorial_games   Node: c3b936cebef1

Provenance: formalization of a published result. Source: arXiv:2611.01281 Section 2

The M-by-N rectangular grid graph is the Cartesian (box) product of the path graph of length M and the path graph of length N on vertex set Fin M × Fin N.
-/

/-- The M-by-N rectangular grid graph. -/
abbrev grid_graph (M N : ℕ) : SimpleGraph (Fin M × Fin N) :=
  SimpleGraph.pathGraph M □ SimpleGraph.pathGraph N
