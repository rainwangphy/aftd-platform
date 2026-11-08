import AFTD.Prelude

/-!
# torus_graph

Topic: combinatorial_games   Node: 4c7133e6a916

Provenance: original. Related work: arXiv:2611.01281

The M-by-N torus grid graph is the Cartesian box product of the cycle graph of length M and the cycle graph of length N on vertex set Fin M × Fin N.
-/

/-- The Cartesian box product of cycle graphs cycleGraph m and cycleGraph n on Fin m × Fin n. -/
abbrev torus_graph (m n : ℕ) : SimpleGraph (Fin m × Fin n) := SimpleGraph.cycleGraph m □ SimpleGraph.cycleGraph n
